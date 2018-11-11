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
  type SubmitMethod = Commit | Cancel | Reset

  [<RequireQualifiedAccess>]
  type Message =
    | Submit  of SubmitMethod
    | Update  of string
    | Left    of Message
    | Right   of Message

  [<RequireQualifiedAccess>]
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
    | D of (Message -> unit)

    static member Submit (D d) a  : unit        = d (Message.Submit a)
    static member Update (D d) v  : unit        = d (Message.Update v)
    static member Left   (D d)    : Dispatcher  = D (fun mu -> d (Message.Left mu))
    static member Right  (D d)    : Dispatcher  = D (fun mu -> d (Message.Right mu))

  type Formlet<'T> = F of (FormletPath -> IHTMLProp list -> Model -> Dispatcher -> 'T*ViewTree*FailureTree)

  module Formlet =
    module Details =
      let inline adapt  (F f)         = f
      let inline invoke f fp ps m d   = f fp ps m d

      let inline submit d a           = Dispatcher.Submit d a
      let inline update d v           = Dispatcher.Update d v
      let inline left d               = Dispatcher.Left d
      let inline right d              = Dispatcher.Right d

      let inline zero ()              = LanguagePrimitives.GenericZero<_>

      let inline join l r             =  (^T : (static member Join : ^T * ^T -> ^T) (l, r))

      let inline flatten (l : ^T)     = (^T : (static member Flatten : ^T  -> ^U) l)

      let inline concat ps (tps : IHTMLProp seq) =
        if List.isEmpty ps then tps
        else Seq.append ps tps

      module Joins =
        let apply     f s = f s
        let andAlso   f s = f, s
        let keepLeft  f _ = f
        let keepRight _ s = s

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

    let join f t u : Formlet<_> =
      let t = adapt t
      let u = adapt u
      F <| fun fp ps m d ->
        let tm, um =
          match m with
          | Model.Fork (l, r) -> l, r
          | _                 -> zero (), zero ()

        let tv, tvt, tft  = invoke t fp ps tm (left d)
        let uv, uvt, uft  = invoke u fp ps um (right d)

        (f tv uv), join tvt uvt, join tft uft

    let apply     t u : Formlet<_> = join Joins.apply     t u
    let andAlso   t u : Formlet<_> = join Joins.andAlso   t u
    let keepLeft  t u : Formlet<_> = join Joins.keepLeft  t u
    let keepRight t u : Formlet<_> = join Joins.keepRight t u

    let map t f : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        let tv, tvt, tft  = invoke t fp ps m d

        f tv, tvt, tft

    let withAttribute p t : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        invoke t fp (p::ps) m d

    let withContainer c cps t : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        // Resets the attributes passed
        let tv, tvt, tft  = invoke t fp [] m d
        let tes : _ seq   = upcast flatten tvt
        let vt            = ViewTree.Element (c (concat ps cps) tes)

        tv, vt, tft

    let initial : Model = zero ()

    let view t c m d : ReactElement =
      let t         = adapt t
      let _, tvt, _ = invoke t [] [] m (D d)
      let es        = flatten tvt

      c es

    let update msg m : Model =
      let mutable submit = None
      let rec loop msg m =
        match msg, m with
        | Message.Submit a  , m                 -> 
          submit <- Some a  // TODO: Not very nice
          m  
        | Message.Update v  , _                 -> Model.Value v
        | Message.Left  u   , Model.Fork (l, r) -> Model.Fork (loop u l, r)
        | Message.Right u   , Model.Fork (l, r) -> Model.Fork (l, loop u r)
        // mu is either left or right, create a new fork and update it
        | _                 , _                 -> loop msg (Model.Fork (zero (), zero ()))
      let m = loop msg m
      match submit with
      | None        -> m
      | Some method ->
        match method with
        | SubmitMethod.Reset  -> initial
        | SubmitMethod.Commit -> m      // TODO:
        | SubmitMethod.Cancel -> m      // TODO:


    let collect t m =
      let t           = adapt t
      let tv, _, tft  = invoke t [] [] m (D (fun _ -> ()))
      let fs          = flatten tft

      tv, fs

    type Builder () =
      class
        member x.Bind       (t, uf) = bind  t uf
        member x.Return     v       = value v
        member x.ReturnFrom t       = t : Formlet<_>
        member x.Zero       ()      = value ()
      end

  let formlet = Formlet.Builder ()

  type Formlet<'T> with
    static member (>>=) (t, uf) = Formlet.bind  t uf
    static member (<*>) (f, t)  = Formlet.apply f t
    static member (|>>) (t, f)  = Formlet.map   t f

    static member (<&>) (f, t)  = Formlet.andAlso   f t
    static member (.>>.)(f, t)  = Formlet.andAlso   f t
    static member (.>>) (f, t)  = Formlet.keepLeft  f t


  module Bootstrap =
    open Formlet
    open Formlet.Details

    let text hint initial : Formlet<string> =
      F <| fun fp ps m d ->
        let v   =
          match m with
          | Model.Value v -> v
          | _             -> initial

        let ie  =
          input <|
            concat ps
              [|
                Class         "form-control"
                Placeholder   hint
// TODO: OnBlur preferable as it forces less rebuilds, but default value causes resets to be missed
//                DefaultValue  v
//                OnBlur        <| fun v -> update d (box v.target :?> Fable.Import.Browser.HTMLInputElement).value
                Value         v
                OnChange      <| fun v -> update d v.Value
              |]
        let vt  = ViewTree.Element ie

        v, vt, zero ()

    let withLabel id lbl t : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        let fp            = (FormletPathElement.Named lbl)::fp
        let ps            = (Id id :> IHTMLProp)::ps
        let tv, tvt, tft  = invoke t fp ps m d
        let le            = label [|HTMLAttr.HtmlFor id|] [|str lbl|]
        let vt            = join (ViewTree.Element le) tvt 

        tv, vt, tft

    let withFormGroup t = Formlet.withContainer div [|Class "form-group"|] t

    let withSubmit t : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        let tv, tvt, tft  = invoke t fp ps m d
        let be            = 
          div 
            [||]
            [|
              button [|OnClick (fun _ -> submit d SubmitMethod.Commit); Type "button"; Class "btn btn-primary"|] [|str "Commit"|]
              button [|OnClick (fun _ -> submit d SubmitMethod.Cancel); Type "button"; Class "btn"|]             [|str "Cancel"|]
              button [|OnClick (fun _ -> submit d SubmitMethod.Reset ); Type "button"; Class "btn"|]             [|str "Reset"|]
            |]
        let vt            = join tvt (ViewTree.Element be) 

        tv, vt, tft

open Formlets

let sampleForm =
  let input lbl hint = Bootstrap.text hint "" |> Bootstrap.withLabel lbl lbl |> Bootstrap.withFormGroup
  Formlet.value (fun f s -> f, s)
  <*> input "First name" "Enter first name"
  <*> input "Last name"  "Enter last name"
  |> Bootstrap.withSubmit

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
