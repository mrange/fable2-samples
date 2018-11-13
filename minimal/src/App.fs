module App

open Elmish
open Elmish.React
open Fable.Helpers.React
open Fable.Helpers.React.Props

module Formlets =
  open Fable.Import.React
  open System.Text

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

  type FormletContext =
    {
      Attributes  : IHTMLProp list
      Classes     : string list
      Path        : FormletPath
      Styles      : CSSProp list
    }

    member x.AddClass (attrs : IHTMLProp list) =
      if x.Classes.IsEmpty then attrs
      else
        let sb = StringBuilder 16
        for c in x.Classes do
          sb.Append " " |> ignore
          sb.Append c |> ignore

        (Class (sb.ToString ()) :> IHTMLProp)::attrs

    member x.AddStyle  (attrs : IHTMLProp list) =
      if x.Styles.IsEmpty then attrs
      else
        (Style x.Styles :> IHTMLProp)::attrs

    member x.AllAttributes ps =
      let attrs =
        x.Attributes
        |> x.AddClass
        |> x.AddStyle
      if attrs.IsEmpty then ps
      else Seq.append attrs ps

    member inline x.InnerElement  ()  = { FormletContext.Zero with Path = x.Path  }
    member inline x.WithAttribute a   = { x with Attributes = a::x.Attributes     }
    member inline x.WithClass     c   = { x with Classes    = c::x.Classes        }
    member inline x.WithPath      p   = { x with Path       = p::x.Path           }
    member inline x.WithStyle     s   = { x with Styles     = s::x.Styles         }

    static member New p c s a : FormletContext = { Path = p; Classes = c; Styles =s; Attributes = a }
    static member Zero = FormletContext.New [] [] [] []

  type Formlet<'T> = F of (FormletContext -> Model -> Dispatcher -> 'T*ViewTree*FailureTree)

  type Form<'Model, 'Msg> = Form of ('Model -> ('Msg -> unit) -> ReactElement)

  module Details =
    let inline adapt  (F f)         = f
    let inline invoke f ctx m d     = f ctx m d
    // TODO: Why doesn't this work?
    //let inline adapt  (F f)         = OptimizedClosures.FSharpFunc<_, _, _, _, _>.Adapt f
    //let inline invoke f fp ps m d   = (f : OptimizedClosures.FSharpFunc<_, _, _, _, _>).Invoke (fp, ps, m, d)

    let pathToString ps =
      let sb = StringBuilder 16
      let inline app s = sb.Append (s : string) |> ignore
      let rec loop ps =
        match ps with
        | []                                -> ()
        | (FormletPathElement.Named n)::ps  -> loop ps; app "."; app n
      loop ps
      sb.ToString ()
    let inline update d v           = Dispatcher.Update d v
    let inline left   d             = Dispatcher.Left d
    let inline right  d             = Dispatcher.Right d

    let inline zero     ()          = LanguagePrimitives.GenericZero<_>
    let inline join     l r         = (^T : (static member Join : ^T * ^T -> ^T) (l, r))
    let inline flatten  l           = (^T : (static member Flatten : ^T  -> ^U) l)
    let inline toString l           = (^T : (member ToString : unit  -> string) l)
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
      module Joins =
        let apply     f s = f s
        let andAlso   f s = f, s
        let keepLeft  f _ = f
        let keepRight _ s = s

    open Details

    let value v : Formlet<_> =
      F <| fun ctx m d ->
        v, zero (), zero ()

    let bind t uf : Formlet<_> =
      let t = adapt t
      F <| fun ctx m d ->
        let tm, um =
          match m with
          | Model.Fork (l, r) -> l, r
          | _                 -> zero (), zero ()

        let tv, tvt, tft  = invoke t ctx tm (left d)
        let u             = uf tv
        let u             = adapt u
        let uv, uvt, uft  = invoke u ctx um (right d)

        uv, join tvt uvt, join tft uft

    let combine f t u : Formlet<_> =
      let t = adapt t
      let u = adapt u
      F <| fun ctx m d ->
        let tm, um =
          match m with
          | Model.Fork (l, r) -> l, r
          | _                 -> zero (), zero ()

        let tv, tvt, tft  = invoke t ctx tm (left d)
        let uv, uvt, uft  = invoke u ctx um (right d)

        (f tv uv), join tvt uvt, join tft uft

    let apply     t u : Formlet<_> = combine Joins.apply     t u
    let andAlso   t u : Formlet<_> = combine Joins.andAlso   t u
    let keepLeft  t u : Formlet<_> = combine Joins.keepLeft  t u
    let keepRight t u : Formlet<_> = combine Joins.keepRight t u

    let map t f : Formlet<_> =
      let t = adapt t
      F <| fun ctx m d ->
        let tv, tvt, tft  = invoke t ctx m d

        f tv, tvt, tft

    let withAttribute p t : Formlet<_> =
      let t = adapt t
      F <| fun ctx m d ->
        let ctx = ctx.WithAttribute p
        invoke t ctx m d

    let withClass c t : Formlet<_> =
      let t = adapt t
      F <| fun ctx m d ->
        let ctx = ctx.WithClass c
        invoke t ctx m d

    let withStyle s t : Formlet<_> =
      let t = adapt t
      F <| fun ctx m d ->
        let ctx = ctx.WithStyle s
        invoke t ctx m d

    let withContainer c t : Formlet<_> =
      let t = adapt t
      F <| fun ctx m d ->
        // Resets the attributes passed
        let attrs         = ctx.AllAttributes []
        let ctx           = ctx.InnerElement ()
        let tv, tvt, tft  = invoke t ctx m d
        let tes           = flatten tvt
        let vt            = ViewTree.Element (c attrs tes)

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

  module Validate =
    let nop t : Formlet<_> = t

    let notEmpty t : Formlet<string> =
      let t = adapt t
      F <| fun ctx m d ->
        let ctx           = ctx.WithAttribute <| Required true
//        let ctx           = ctx.WithClass <| Required true
        let tv, tvt, tft  = invoke t ctx m d
        let valid         = String.length tv > 0
        let tft           =
          if valid then tft else join tft (FailureTree.Leaf (ctx.Path, "Is Empty"))

        tv, tvt, tft

  module Bootstrap =
    open Formlet

    let withPanel lbl t : Formlet<_> =
      let t = adapt t
      F <| fun ctx m d ->
        let attrs         = ctx.AllAttributes [|Class "card"; Style [MarginBottom "12px"]|]
        let ctx           = ctx.InnerElement ()
        let ctx           = ctx.WithPath <| FormletPathElement.Named lbl
        let ctx           = ctx.InnerElement ()
        let tv, tvt, tft  = invoke t ctx m d
        let tes           = flatten tvt
        let pe            =
          div
            attrs
            [|
              div [|Class "card-header" |]  [|str lbl|]
              div [|Class "card-body"   |]  tes
            |]
        let vt            = ViewTree.Element pe

        tv, vt, tft

    let text hint initial : Formlet<string> =
      F <| fun ctx m d ->
        let v     =
          match m with
          | Model.Value v -> v
          | _             -> initial

        let attrs =
          ctx.AllAttributes
            [|
              Class         "form-control"
// TODO: OnBlur preferable as it forces less rebuilds, but default value causes resets to be missed
// TODO: Fix reset
              DefaultValue  v
              OnBlur        <| fun v -> update d (box v.target :?> Fable.Import.Browser.HTMLInputElement).value
//              OnChange      <| fun v -> update d v.Value
              Placeholder   hint
//              Value         v
            |]

        let ie    = input attrs
        let vt    = ViewTree.Element ie

        v, vt, zero ()

    let checkBox id lbl : Formlet<bool> =
      F <| fun ctx m d ->
        let attrs     = ctx.AllAttributes [|Class "form-check"|]
        let isChecked =
          match m with
          | Model.Value "on"  -> true
          | _                 -> false
        let e         =
          div
            attrs
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
      F <| fun ctx m d ->
        let ctx           = ctx.WithPath <| FormletPathElement.Named lbl
        let ctx           = ctx.WithAttribute <| Id id
        let tv, tvt, tft  = invoke t ctx m d
        let le            = label [|HTMLAttr.HtmlFor id|] [|str lbl|]
        let vt            = join (ViewTree.Element le) tvt

        tv, vt, tft

    let withOption id lbl t : Formlet<_ option> =
      checkBox id lbl >>= (fun v -> if v then map t Some else value None)

    let withFormGroup t = Formlet.withContainer div t |> Formlet.withClass "form-group"

    let asForm extractModel onUpdate onCommit onCancel onReset (t : Formlet<'T>) : Form<'Model, 'Msg> =
      let t = adapt t
      Form <| fun m d ->
        let tv, tvt, tft  = invoke t (zero ()) (extractModel m) (D <| fun mu -> onUpdate d mu)

        let tes           = flatten tvt
        let tfs           = flatten tft
        let onCommit d    = if tfs.Length = 0 then onCommit d tv else ()
        let lis           =
          tfs
          |> Array.map (fun (s, p, m) ->
            let p   = pathToString p
            let cls = if s then "list-group-item list-group-item-warning" else "list-group-item list-group-item-danger"
            li [|Class cls|] [|str (sprintf "� %s - %s" p m)|])
        let ul            = ul [|Class "list-group"; Style [CSSProp.MarginBottom "12px"]|] lis
        let be            =
          let inline btn action cls lbl dis =
            button
              [|
                Class   cls
                Disabled dis
                OnClick <|fun _ -> action d
                Style   [CSSProp.MarginRight "8px"]
                Type    "button"
              |]
              [|str lbl|]
          div
            [|Style [CSSProp.MarginBottom "12px"]|]
            [|
              btn onCommit "btn btn-primary" "Commit" (tfs.Length > 0)
              btn onCancel "btn"             "Cancel" false
              btn onReset  "btn"             "Reset"  false
            |]

        form
          [||]
          [|
            be
            ul
            (if tes.Length > 0 then div [||] tes else tes.[0])
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

  let input lbl hint v =
    Bootstrap.text hint ""
    |> v
    |> Bootstrap.withLabel lbl lbl
    |> Bootstrap.withFormGroup

  let address lbl =
    Formlet.value Address.New
    <*> input "Carry over"  ""  Validate.nop
    <*> input "Name"        ""  Validate.notEmpty
    <*> input "Street"      ""  Validate.notEmpty
    <*> input "Street"      ""  Validate.nop
    <*> input "Street"      ""  Validate.nop
    <*> input "Zip"         ""  Validate.notEmpty
    <*> input "City"        ""  Validate.notEmpty
    <*> input "County"      ""  Validate.nop
    <*> input "Country"     ""  Validate.notEmpty
    |> Bootstrap.withPanel lbl

  let customer =
    Formlet.value Customer.New
    <*> input "First name" "Enter first name" Validate.notEmpty
    <*> input "Last name"  "Enter last name"  Validate.notEmpty
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
