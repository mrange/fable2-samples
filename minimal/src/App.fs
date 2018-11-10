module App

open Elmish
open Elmish.React
open Fable.Helpers.React
open Fable.Helpers.React.Props

module Formlets =
  open Fable.Import.React

  [<RequireQualifiedAccess>]
  type FormletPathElement =
    | Named   of string

  type FormletPath = FormletPathElement list

  [<RequireQualifiedAccess>]
  type FailureTree =
    | Empty
    | Leaf        of FormletPath*string
    | Suppress    of FailureTree
    | Fork        of FailureTree*FailureTree

    static member IsGood x =
      match x with
      | Empty
      | Suppress _  -> true
      | Leaf _
      | Fork (_, _) -> false

    static member Zero        : FailureTree = Empty
    static member Join (l, r) : FailureTree =
      match l, r with
      | Empty       , _           -> r
      | _           , Empty       -> l
      | Suppress l  , Suppress r  -> Suppress (Fork (l, r))
      | _           , _           -> Fork (l, r)
    static member Flatten ft  : (bool*FormletPath*string) list =
      let rec loop suppress all ft =
        match ft with
        | FailureTree.Empty       -> all
        | FailureTree.Leaf (p, m) -> (suppress, p, m)::all
        | FailureTree.Suppress ft -> loop true all ft
        | FailureTree.Fork (l, r) -> loop suppress (loop suppress all l) r
      let all = loop false [] ft
      List.rev all

  [<RequireQualifiedAccess>]
  type Model =
    | Empty
    | Value   of string
    | Fork    of Model*Model

    static member Zero        : Model = Empty
    static member Join (l, r) : Model = Fork (l, r)

  [<RequireQualifiedAccess>]
  type ModelUpdate =
    | Value     of string
    | Left      of ModelUpdate
    | Right     of ModelUpdate

  type ViewTree =
    | Empty
    | Element   of ReactElement
    | Fork      of ViewTree*ViewTree

    static member Zero        : ViewTree = Empty
    static member Join (l, r) : ViewTree = 
      match l, r with
      | Empty       , _           -> r
      | _           , Empty       -> l
      | _           , _           -> Fork (l, r)
    static member Flatten vt  : ReactElement list =
      let rec loop all vt =
        match vt with
        | ViewTree.Empty        -> all
        | ViewTree.Element e    -> e::all
        | ViewTree.Fork (l, r)  -> loop (loop all l) r
      let all = loop [] vt
      List.rev all

  type Dispatcher = 
    | D of (ModelUpdate -> unit)

    static member Value (D d) v     : unit        = d (ModelUpdate.Value v)
    static member Left  (D d)       : Dispatcher  = D (fun mu -> d (ModelUpdate.Left mu))
    static member Right (D d)       : Dispatcher  = D (fun mu -> d (ModelUpdate.Right mu))

  type Formlet<'T> = F of (FormletPath -> IHTMLProp list -> Model -> Dispatcher -> 'T*ViewTree*FailureTree)

  module Formlet =
    module Details =
      let inline adapt  (F f)         = f
      let inline invoke f fp ps m d   = f fp ps m d

      let inline left d               = Dispatcher.Left d
      let inline right d              = Dispatcher.Right d
      let inline dispatch d v         = Dispatcher.Value d v

      let inline zero ()              = LanguagePrimitives.GenericZero<_>

      let inline join l r             =  (^T : (static member Join : ^T * ^T -> ^T) (l, r))

      let inline flatten (l : ^T)     = (^T : (static member Flatten : ^T  -> ^U) l)

      let inline concat ps tps        =
        if List.isEmpty ps then tps
        else Seq.append ps tps

    open Details

    let value v : Formlet<_> =
      F <| fun fp ps m d ->
        v, zero (), zero ()

    let bind t uf : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        let tm, um =
          match m with
          | Model.Fork (l, r) -> l, r
          | _                 -> zero (), zero ()

        let tv, tvt, tft  = invoke t fp ps tm (left d)
        let u             = uf tv
        let u             = adapt u
        let uv, uvt, uft  = invoke u fp ps um (right d)

        uv, join tvt uvt, join tft uft

    let apply t u : Formlet<_> =
      let t = adapt t
      let u = adapt u
      F <| fun fp ps m d ->
        let tm, um =
          match m with
          | Model.Fork (l, r) -> l, r
          | _                 -> zero (), zero ()

        let tv, tvt, tft  = invoke t fp ps tm (left d)
        let uv, uvt, uft  = invoke u fp ps um (right d)

        tv uv, join tvt uvt, join tft uft

    let map t f : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        let tv, tvt, tft  = invoke t fp ps m d

        f tv, tvt, tft

    let withAttribute p t : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        invoke t fp (p::ps) m d

    let container c cps t : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        // Resets the attributes passed
        let tv, tvt, tft  = invoke t fp [] m d
        let tes : _ seq   = upcast flatten tvt
        let vt            = ViewTree.Element (c (concat ps cps) tes)

        tv, vt, tft

    let textInput initial : Formlet<string> =
      F <| fun fp ps m d ->
        let v   = 
          match m with 
          | Model.Value v -> v 
          | _             -> initial

        let vt  = ViewTree.Element (input (concat ps [|Value v; OnChange <| fun v -> dispatch d v.Value|]))

        v, vt, zero ()

    let initial : Model = zero ()

    let view t c m d : ReactElement =
      let t         = adapt t
      let _, tvt, _ = invoke t [] [] m (D d)
      let es        = flatten tvt

      c es

    let rec update mu m : Model =
      match mu, m with
      | ModelUpdate.Value v , _                 -> Model.Value v
      | ModelUpdate.Left  u , Model.Fork (l, r) -> Model.Fork (update u l, r)
      | ModelUpdate.Right u , Model.Fork (l, r) -> Model.Fork (l, update u r)
      // mu is either left or right, create a new fork and update it
      | _                   , _                 -> update mu (Model.Fork (zero (), zero ()))

    let collect t m =
      let t           = adapt t
      let tv, _, tft  = invoke t [] [] m (D (fun _ -> ()))
      let fs          = flatten tft

      tv, fs

  type Formlet<'T> with
    static member (>>=) (t, uf) = Formlet.bind  t uf
    static member (<*>) (f, t)  = Formlet.apply f t
    static member (|>>) (t, f)  = Formlet.map   t f

open Formlets

let sampleForm = 
  Formlet.value (fun f s -> f, s)
  <*> (Formlet.textInput "Hello" |> Formlet.withAttribute (Class "test"))
  <*> Formlet.textInput "There"

let init () = Model.Empty

let update msg model = 
  let before = model
  printfn "Update - msg   : %A" msg
  printfn "Update - before: %A" before
  let after  = Formlet.update msg model
  printfn "Update - after : %A" after

  after

let view model dispatch = Formlet.view sampleForm (form []) model dispatch
  
// App
Program.mkSimple init update view
|> Program.withReact "elmish-app"
|> Program.withConsoleTrace
|> Program.run
