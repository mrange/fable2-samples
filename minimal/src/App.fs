module App

(**
 The famous Increment/Decrement ported from Elm.
 You can find more info about Emish architecture and samples at https://elmish.github.io/
*)

open Elmish
open Elmish.React
open Fable.Helpers.React
open Fable.Helpers.React.Props

module Formlets2 =
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
    static member Left (D d)        : Dispatcher  = D (fun mu -> d (ModelUpdate.Left mu))
    static member Right (D d)       : Dispatcher  = D (fun mu -> d (ModelUpdate.Right mu))

  type Formlet<'T> = F of (FormletPath -> Model -> Dispatcher -> 'T*ViewTree*FailureTree)

  module Formlet =
    module Details =
      let inline adapt  (F f)     = f
      let inline invoke f fp m d  = f fp m d

      let inline isGood ft      = FailureTree.IsGood ft

      let inline left d         = Dispatcher.Left d
      let inline right d        = Dispatcher.Right d
      let inline dispatch d v   = Dispatcher.Value d v


      let inline zero ()        = LanguagePrimitives.GenericZero<_>

      let inline join l r = 
        (^T : (static member Join : ^T * ^T -> ^T) (l, r))

      let inline flatten (l : ^T) = 
        (^T : (static member Flatten : ^T  -> ^U) l)
    open Details

    let value v : Formlet<_> =
      F <| fun fp m d ->
        v, zero (), zero ()

    let bind t uf : Formlet<_> =
      let t = adapt t
      F <| fun fp m d ->

        let tm, um =
          match m with
          | Model.Fork (l, r) -> l, r
          | _                 -> zero (), zero ()

        let tv, tvt, tft  = invoke t fp tm (left d)
        let u             = uf tv
        let u             = adapt u
        let uv, uvt, uft  = invoke u fp um (right d)

        uv, join tvt uvt, join tft uft

    let apply t u : Formlet<_> =
      let t = adapt t
      let u = adapt u
      F <| fun fp m d ->

        let tm, um =
          match m with
          | Model.Fork (l, r) -> l, r
          | _                 -> zero (), zero ()

        let tv, tvt, tft  = invoke t fp tm (left d)
        let uv, uvt, uft  = invoke u fp um (right d)

        tv uv, join tvt uvt, join tft uft

    let textInput initial : Formlet<string> =
      F <| fun fp m d ->
        let v = 
          match m with 
          | Model.Value v -> v 
          | _             -> initial

        let vt = ViewTree.Element (input [|Value v; OnChange <| fun v -> dispatch d v.Value|])

        v, vt, zero ()

    let initial : Model = zero ()

    let view t m d : ReactElement =
      let t = adapt t
      let _, tvt, _ = invoke t [] m (D d)

      let es = flatten tvt
      div [] es

    let rec update mu m : Model =
      match mu, m with
      | ModelUpdate.Value v , _                 -> Model.Value v
      | ModelUpdate.Left  u , Model.Fork (l, r) -> Model.Fork(update u l, r)
      | ModelUpdate.Right u , Model.Fork (l, r) -> Model.Fork(l, update u r)
      // mu is either left or right, create a new fork and update it
      | _                   , _                 -> update mu (Model.Fork (zero (), zero ()))

  type Formlet<'T> with
    static member (>>=) (t, uf) = Formlet.bind t uf
    static member (<*>) (f, t)  = Formlet.apply f t

module Formlets =
  open Fable.Import.React

  [<RequireQualifiedAccess>]
  type FailurePathElement =
    | Named   of string

  type FailurePath = FailurePathElement list

  [<RequireQualifiedAccess>]
  type FailureTree =
    | Empty
    | Leaf        of FailurePath*string
    | Suppress    of FailureTree
    | Fork        of FailureTree*FailureTree

    member x.IsGood =
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
    static member Flatten ft  : (bool*FailurePath*string) list =
      let rec loop suppress all ft =
        match ft with
        | FailureTree.Empty       -> all
        | FailureTree.Leaf (p, m) -> (suppress, p, m)::all
        | FailureTree.Suppress ft -> loop true all ft
        | FailureTree.Fork (l, r) -> loop suppress (loop suppress all l) r
      let all = loop false [] ft
      List.rev all

  [<RequireQualifiedAccess>]
  type StateTree =
    | Empty
    | Value   of string ref
    | Fork    of StateTree*StateTree

    static member Zero        : StateTree = Empty
    static member Join (l, r) : StateTree = Fork (l, r)

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


  type FormletResult<'T> = FR of 'T*ViewTree*StateTree*FailureTree

  type Formlet<'T> = F of (FailurePath -> StateTree -> FormletResult<'T>)

  module Formlet =
    module Details =
      //let inline adapt  f       = OptimizedClosures.FSharpFunc<_, _, _>.Adapt f
      //let inline invoke f fp st = (f : OptimizedClosures.FSharpFunc<_, _, _>).Invoke (fp, st)
      let inline adapt  f       = f
      let inline invoke f fp st = f fp st

      let inline isGood (ft : FailureTree) = ft.IsGood

      let inline zero ()        = LanguagePrimitives.GenericZero<_>

      let inline join l r = 
        (^T : (static member Join : ^T * ^T -> ^T) (l, r))

      let inline flatten (l : ^T) = 
        (^T : (static member Flatten : ^T  -> ^U) l)

    open Details

    let inline value v : Formlet<_> =
      F <| fun fp st ->
        FR (v, zero (), zero (), zero ())

    let inline bind (F t) (uf : 'T -> Formlet<'U>) : Formlet<'U> =
      let t = adapt t
      F <| fun fp st ->
        let tst, ust = 
          match st with
          | StateTree.Fork (tst, ust) -> tst, ust
          | _                         -> zero (), zero ()

        let (FR (tv, tvt, tst, tft)) = invoke t fp tst
        let (F u) = uf tv
        let u = adapt u
        let (FR (uv, uvt, ust, uft)) = invoke u fp ust

        FR (uv, join tvt uvt, join tst ust, join tft uft)

    let inline apply (F f) (F t) : Formlet<'U> =
      let f = adapt f
      let t = adapt t
      F <| fun fp st ->
        let fst, tst = 
          match st with
          | StateTree.Fork (fst, tst) -> fst, tst
          | _                         -> zero (), zero ()

        let (FR (fv, fvt, fst, fft)) = invoke f fp fst
        let (FR (tv, tvt, tst, tft)) = invoke t fp tst

        FR (fv tv, join fvt tvt, join fst tst, join fft tft)

    let textInput initial : Formlet<string> =
      F <| fun fp st ->
        let st, v = 
          match st with 
          | StateTree.Value v -> st, !v 
          | _                 -> StateTree.Value (ref initial), initial

        let vt = ViewTree.Element (input [|Value v|])

        FR (v, vt, st, zero ())

    let eval st (F t) =
      let t = adapt t
      let (FR (v, vt, st, ft)) = invoke t [] st
      let es = flatten vt
      let fs = flatten ft
      let e = div [] es
      (v, e, st, fs)

  type Formlet<'T> with
    static member (>>=) (t, uf) = Formlet.bind t uf
    static member (<*>) (f, t)  = Formlet.apply f t

module Test =
  open Formlets
  open Formlet

  let test = 
    value (fun f s -> f, s)
    <*> textInput "Hello"
    <*> textInput "There"
  
  let render () =
    let (s, re, st, fs) = eval StateTree.Empty test
    printfn "Result   : %A" s
    printfn "StateTree: %A" st
    printfn "Failures : %A" fs
    re

// MODEL

type Model = int

type Msg =
| Increment
| Decrement

let init() : Model = 0

// UPDATE

let update (msg:Msg) (model:Model) =
    match msg with
    | Increment -> model + 1
    | Decrement -> model - 1

// VIEW (rendered with React)

let view (model:Model) dispatch =
  let t = Test.render ()

  div []
      [ button [ OnClick (fun _ -> dispatch Increment) ] [ str "+" ]
        div [] [ str (string model) ]
        button [ OnClick (fun _ -> dispatch Decrement) ] [ str "-" ] ]


// App
Program.mkSimple init update view
|> Program.withReact "elmish-app"
|> Program.withConsoleTrace
|> Program.run
