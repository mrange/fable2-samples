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
    static member Flatten ft  : (bool*FormletPath*string) array =
      let ra = ResizeArray<_> 16
      let rec loop suppress ft =
        match ft with
        | FailureTree.Empty       -> ()
        | FailureTree.Leaf (p, m) -> ra.Add (suppress, p, m)
        | FailureTree.Suppress ft -> loop true ft
        | FailureTree.Fork (l, r) -> 
          loop suppress l
          loop suppress r
      loop false ft
      ra.ToArray ()

  [<RequireQualifiedAccess>]
  type Model =
    | Empty
    | Value   of string
    | Fork    of Model*Model

    static member Zero        : Model = Empty
    static member Join (l, r) : Model = Fork (l, r)

  [<RequireQualifiedAccess>]
  type ModelUpdate =
    | Update  of string
    | Left    of ModelUpdate
    | Right   of ModelUpdate

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
    static member Flatten vt  : ReactElement array =
      let ra = ResizeArray<_> 16
      let rec loop vt =
        match vt with
        | ViewTree.Empty        -> ()
        | ViewTree.Element e    -> ra.Add e
        | ViewTree.Fork (l, r)  -> 
          loop l
          loop r
      loop vt
      ra.ToArray ()

  type Dispatcher =
    | D of (ModelUpdate -> unit)

    static member Update (D d) v  : unit        = d (ModelUpdate.Update v)
    static member Left   (D d)    : Dispatcher  = D (fun mu -> d (ModelUpdate.Left mu))
    static member Right  (D d)    : Dispatcher  = D (fun mu -> d (ModelUpdate.Right mu))

  type Formlet<'T> = F of (FormletPath -> IHTMLProp list -> Model -> Dispatcher -> 'T*ViewTree*FailureTree)

  type Form<'Model, 'Msg> = Form of ('Model -> ('Msg -> unit) -> ReactElement)

  module Details =
    let inline adapt  (F f)         = f
    let inline invoke f fp ps m d   = f fp ps m d
    // TODO: Why doesn't this work?
    //let inline adapt  (F f)         = OptimizedClosures.FSharpFunc<_, _, _, _, _>.Adapt f
    //let inline invoke f fp ps m d   = (f : OptimizedClosures.FSharpFunc<_, _, _, _, _>).Invoke (fp, ps, m, d)

    let inline update d v           = Dispatcher.Update d v
    let inline left d               = Dispatcher.Left d
    let inline right d              = Dispatcher.Right d

    let inline zero ()              = LanguagePrimitives.GenericZero<_>

    let inline join l r             =  (^T : (static member Join : ^T * ^T -> ^T) (l, r))

    let inline flatten (l : ^T)     = (^T : (static member Flatten : ^T  -> ^U) l)
  open Details

  module Form =
    let view (Form f) m d : ReactElement = f m d

    let update msg m : Model =
      let rec loop msg m =
        match msg, m with
        | ModelUpdate.Update v  , _                 -> Model.Value v
        | ModelUpdate.Left   u  , Model.Fork (l, r) -> Model.Fork (loop u l, r)
        | ModelUpdate.Right  u  , Model.Fork (l, r) -> Model.Fork (l, loop u r)
        // mu is either left or right, create a new fork and update it
        | _                 , _                     -> loop msg (Model.Fork (zero (), zero ()))
      loop msg m

    let initial : Model = zero ()

  module Formlet =
    module Details =
      let inline attributes ps tps    =
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

    let combine f t u : Formlet<_> =
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

    let apply     t u : Formlet<_> = combine Joins.apply     t u
    let andAlso   t u : Formlet<_> = combine Joins.andAlso   t u
    let keepLeft  t u : Formlet<_> = combine Joins.keepLeft  t u
    let keepRight t u : Formlet<_> = combine Joins.keepRight t u

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
        let vt            = ViewTree.Element (c (attributes ps cps) tes)

        tv, vt, tft

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

    let withPanel lbl t : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        let fp            = (FormletPathElement.Named lbl)::fp
        let tv, tvt, tft  = invoke t fp [] m d
        let es            = flatten tvt
        let pe            =
          div 
            (attributes ps [|Class "card"; Style [MarginBottom "12px"]|])
            [|
              div [|Class "card-header"|] [|str lbl|]
              div [|Class "card-body"|] es
            |]
        let vt            = ViewTree.Element pe

        tv, vt, tft

    let text hint initial : Formlet<string> =
      F <| fun fp ps m d ->
        let v   =
          match m with
          | Model.Value v -> v
          | _             -> initial

        let ie  =
          input <|
            attributes ps
              [|
                Class         "form-control"
// TODO: OnBlur preferable as it forces less rebuilds, but default value causes resets to be missed
//                DefaultValue  v
//                OnBlur        <| fun v -> update d (box v.target :?> Fable.Import.Browser.HTMLInputElement).value
                OnChange      <| fun v -> update d v.Value
                Placeholder   hint
                Value         v
              |]
        let vt  = ViewTree.Element ie

        v, vt, zero ()

    let checkBox id lbl : Formlet<bool> =
      F <| fun fp ps m d ->
        let isChecked =
          match m with
          | Model.Value "on"  -> true
          | _                 -> false
        let e             =
          div 
            (attributes ps [|Class "form-check"|])
            [|
              input 
                [|
                  Checked   isChecked
                  Class     "form-check-input"
                  Id        id
                  Type      "checkbox"
                  OnChange  <| fun v -> update d (if isChecked then "" else "on")
                |]
              label [|HTMLAttr.HtmlFor id|] [|str lbl|]
            |]
        let vt            = ViewTree.Element e

        isChecked, vt, zero ()

    let withLabel id lbl t : Formlet<_> =
      let t = adapt t
      F <| fun fp ps m d ->
        let fp            = (FormletPathElement.Named lbl)::fp
        let ps            = (Id id :> IHTMLProp)::ps
        let tv, tvt, tft  = invoke t fp ps m d
        let le            = label [|HTMLAttr.HtmlFor id|] [|str lbl|]
        let vt            = join (ViewTree.Element le) tvt 

        tv, vt, tft

    let withOption id lbl t : Formlet<_ option> =
      checkBox id lbl >>= (fun v -> if v then map t Some else value None)

    let withFormGroup t = Formlet.withContainer div [|Class "form-group"|] t

    let asForm extractModel onUpdate onCommit onCancel onReset (t : Formlet<'T>) : Form<'Model, 'Msg> =
      let t = adapt t
      Form <| fun m d ->
        let tv, tvt, tft  = invoke t [] [] (extractModel m) (D <| fun mu -> onUpdate d mu)
        let onCommit d    = onCommit d tv
        let te            = flatten tvt
        let be            = 
          let inline btn action cls lbl = 
            button 
              [|
                Class   cls
                OnClick <|fun _ -> action d
                Style   [CSSProp.MarginRight "8px"]
                Type    "button"
              |] 
              [|str lbl|]
          div
            [||]
            [|
              btn onCommit "btn btn-primary" "Commit"
              btn onCancel "btn"             "Cancel"
              btn onReset  "btn"             "Reset"
            |]

        form 
          [||]
          [|
            (if te.Length > 0 then div [||] te else te.[0])
            be
          |]

open Formlets

type MyModel    = M of Model
type MyMessage  = 
  | Commit
  | Cancel
  | Reset
  | UpdateForm of ModelUpdate

type Address =
  {
    CarryOver : string
    Name      : string
    Street1   : string
    Street2   : string
    Street3   : string
    Zip       : string
    City      : string
    County    : string
    Country   : string
  }
  static member New co n s1 s2 s3 zip city county country =
    {
      CarryOver = co
      Name      = n
      Street1   = s1
      Street2   = s2
      Street3   = s3
      Zip       = zip
      City      = city
      County    = county
      Country   = country
    }

type Customer =
  {
    FirstName       : string
    LastName        : string
    InvoiceAddress  : Address
    DeliveryAddress : Address option
  }
  static member New fn ln ia da =
    {
      FirstName       = fn
      LastName        = ln
      InvoiceAddress  = ia
      DeliveryAddress = da
    }
  

let sampleForm =
  let extractModel  (M m) = m
  let onUpdate d    mu    = d (UpdateForm mu)
  let onCommit d     v    = 
    printfn "Commit: %A" v
    d Commit
  let onCancel d          = d Cancel
  let onReset  d          = d Reset

  let input lbl hint = 
    Bootstrap.text hint "" 
    |> Bootstrap.withLabel lbl lbl 
    |> Bootstrap.withFormGroup

  let address lbl =
    Formlet.value Address.New
    <*> input "Carry over"  ""
    <*> input "Name"        ""
    <*> input "Street"      ""
    <*> input "Street"      ""
    <*> input "Street"      ""
    <*> input "Zip"         ""
    <*> input "City"        ""
    <*> input "County"      ""
    <*> input "Country"     ""
    |> Bootstrap.withPanel lbl

  let customer = 
    Formlet.value Customer.New
    <*> input "First name" "Enter first name"
    <*> input "Last name"  "Enter last name"
    |> Bootstrap.withPanel "Customer"
    <*> address "Invoice address"
    <*> (address "Delivery address" |> Bootstrap.withOption "delivery-address?" "Use delivery address?")

  customer |> Bootstrap.asForm extractModel onUpdate onCommit onCancel onReset


let init () = M Model.Empty

let update msg (M model) =
  match msg with
  | Commit        -> M model
  | Cancel        -> M model
  | Reset         -> init ()
  | UpdateForm mu -> 
    let before = model
    printfn "Update - msg   : %A" msg
    printfn "Update - before: %A" before
    let after  = Form.update mu model
    printfn "Update - after : %A" after
    M after

let view model dispatch = 
  div 
    [|Style [CSSProp.Margin "12px"]|]
    [|Form.view sampleForm model dispatch|]
  

// App
Program.mkSimple init update view
|> Program.withReact "elmish-app"
|> Program.withConsoleTrace
|> Program.run
