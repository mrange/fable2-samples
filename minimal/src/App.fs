module App

open Elmish
open Elmish.React
open Fable.Helpers.React
open Fable.Helpers.React.Props

module Formlets =
  open Fable.Import.React
  open System.Text
  open System.Text.RegularExpressions

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
    | Element         of ReactElement
    | DelayedElement  of (IHTMLProp list -> string -> CSSProp list -> ReactElement)
    | WithAttribute   of IHTMLProp*ViewTree
    | WithClass       of string*ViewTree
    | WithStyle       of CSSProp*ViewTree
    | Fork            of ViewTree*ViewTree

    static member Zero        : ViewTree = Empty
    static member Join (l, r) : ViewTree =
      match l, r with
      | Empty       , _           -> r
      | _           , Empty       -> l
      | _           , _           -> Fork (l, r)
    static member Flatten vt : ReactElement array =
      let ra = ResizeArray<_> 16
      let rec loop aa cc ss vt =
        match vt with
        | ViewTree.Empty                  -> ()
        | ViewTree.Element        e       -> ra.Add e
        | ViewTree.DelayedElement d       -> ra.Add (d aa cc ss)
        | ViewTree.WithAttribute  (a, t)  -> loop (a::aa) cc ss t
        | ViewTree.WithClass      (c, t)  -> loop aa (c + " " + cc) ss t
        | ViewTree.WithStyle      (s, t)  -> loop aa cc (s::ss) t
        | ViewTree.Fork           (l, r)  ->
          loop aa cc ss l
          loop aa cc ss r
      loop [] "" [] vt
      ra.ToArray ()

  type Dispatcher =
    | D of (ModelUpdate -> unit)

    static member Update (D d) v  : unit        = d (ModelUpdate.Update v)
    static member Left   (D d)    : Dispatcher  = D (fun mu -> d (ModelUpdate.Left mu))
    static member Right  (D d)    : Dispatcher  = D (fun mu -> d (ModelUpdate.Right mu))

  type Formlet<'T> = F of (FormletPath -> Model -> Dispatcher -> 'T*ViewTree*FailureTree)

  type Form<'Model, 'Msg> = Form of ('Model -> ('Msg -> unit) -> ReactElement)

  module Details =
    let inline adapt  (F f)         = f
    let inline invoke f fp m d      = f fp m d

    let inline flip f a b           = f b a
    // TODO: Why doesn't this work?
    //let inline adapt  (F f)         = OptimizedClosures.FSharpFunc<_, _, _, _, _>.Adapt f
    //let inline invoke f fp ps m d   = (f : OptimizedClosures.FSharpFunc<_, _, _, _, _>).Invoke (fp, ps, m, d)

    let inline isGood ft            = FailureTree.IsGood ft

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


    let inline delayedElement_ e    =
      ViewTree.DelayedElement <| fun aa cc ss ->
        let aa = (Class cc :> IHTMLProp)::(Style ss :> IHTMLProp)::aa
        e aa
    let inline delayedElement e a c s  =
      ViewTree.DelayedElement <| fun aa cc ss ->
        let aa = a@aa
        let cc = c + " " + cc
        let ss = s@ss
        let aa = (Class cc :> IHTMLProp)::(Style ss :> IHTMLProp)::aa
        e aa

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

    let combine f t u : Formlet<_> =
      let t = adapt t
      let u = adapt u
      F <| fun fp m d ->
        let tm, um =
          match m with
          | Model.Fork (l, r) -> l, r
          | _                 -> zero (), zero ()

        let tv, tvt, tft  = invoke t fp tm (left d)
        let uv, uvt, uft  = invoke u fp um (right d)

        (f tv uv), join tvt uvt, join tft uft

    let apply     t u : Formlet<_> = combine Joins.apply     t u
    let andAlso   t u : Formlet<_> = combine Joins.andAlso   t u
    let keepLeft  t u : Formlet<_> = combine Joins.keepLeft  t u
    let keepRight t u : Formlet<_> = combine Joins.keepRight t u

    let map t f : Formlet<_> =
      let t = adapt t
      F <| fun fp m d ->
        let tv, tvt, tft  = invoke t fp m d

        f tv, tvt, tft

    let withAttribute p t : Formlet<_> =
      let t = adapt t
      F <| fun fp m d ->
        let tv, tvt, tft  = invoke t fp m d
        let tvt           = ViewTree.WithAttribute (p, tvt)

        tv, tvt, tft

    let withClass c t : Formlet<_> =
      let t = adapt t
      F <| fun fp m d ->
        let tv, tvt, tft  = invoke t fp m d
        let tvt           = ViewTree.WithClass (c, tvt)

        tv, tvt, tft

    let withStyle s t : Formlet<_> =
      let t = adapt t
      F <| fun fp m d ->
        let tv, tvt, tft  = invoke t fp m d
        let tvt           = ViewTree.WithStyle (s, tvt)

        tv, tvt, tft

    let withContainer c t : Formlet<_> =
      let t = adapt t
      F <| fun fp m d ->
        // Resets the attributes passed
        let tv, tvt, tft  = invoke t fp m d
        let tes           = flatten tvt
        let d             = (flip c) tes
        let tvt           = delayedElement_ d

        tv, tvt, tft

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
    let yes t : Formlet<_> = t

    let notEmpty t : Formlet<string> =
      let t = adapt t
      F <| fun fp m d ->
        let tv, tvt, tft  = invoke t fp m d
        let valid         = String.length tv > 0
        let tft           = if valid then tft else join tft (FailureTree.Leaf (fp, "You must provide a value."))
        let tvt           = ViewTree.WithAttribute (Required true, tvt)
        let tvt           = ViewTree.WithClass ((if valid then "is-valid" else "is-invalid"), tvt)

        tv, tvt, tft

    let regex (r : Regex) (msg : string) t : Formlet<string> =
      let t = adapt t
      F <| fun fp m d ->
        let tv, tvt, tft  = invoke t fp m d
        let valid         = r.IsMatch tv
        let tft           = if valid then tft else join tft (FailureTree.Leaf (fp, msg))
        let tvt           = ViewTree.WithAttribute (Required true, tvt)
        let tvt           = ViewTree.WithClass ((if valid then "is-valid" else "is-invalid"), tvt)

        tv, tvt, tft
  module Bootstrap =
    open Formlet

    let withPanel lbl t : Formlet<_> =
      let t = adapt t
      F <| fun fp m d ->
        let fp            = (FormletPathElement.Named lbl)::fp
        let tv, tvt, tft  = invoke t fp m d
        let tes           = flatten tvt
        let d             =
          flip div
            [|
              div [|Class "card-header" |]  [|str lbl|]
              div [|Class "card-body"   |]  tes
            |]
        let tvt           = delayedElement d [] "card" [MarginBottom "12px"]

        tv, tvt, tft

    let text hint initial : Formlet<string> =
      F <| fun fp m d ->
        let v =
          match m with
          | Model.Value v -> v
          | _             -> initial

        let aa : IHTMLProp list =
            [
// TODO: OnBlur preferable as it forces less rebuilds, but default value causes resets to be missed
// TODO: Fix reset
              DefaultValue  v
              OnBlur        <| fun v -> update d (box v.target :?> Fable.Import.Browser.HTMLInputElement).value
//              OnChange      <| fun v -> update d v.Value
              Placeholder   hint
//              Value         v
            ]

        let tvt = delayedElement input aa "form-control" []

        v, tvt, zero ()

    let checkBox id lbl : Formlet<bool> =
      F <| fun fp m d ->
        let isChecked =
          match m with
          | Model.Value "on"  -> true
          | _                 -> false
        let d         =
          flip div
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
        let tvt       = delayedElement d [] "form-check" []

        isChecked, tvt, zero ()

    let withLabel id lbl t : Formlet<_> =
      let t = adapt t
      F <| fun fp m d ->
        let fp            = (FormletPathElement.Named lbl)::fp
        let tv, tvt, tft  = invoke t fp m d
        let e             = label [|HTMLAttr.HtmlFor id|] [|str lbl|]
        let tvt           = ViewTree.WithAttribute (Id id, tvt)
        let tvt           = join (ViewTree.Element e) tvt

        tv, tvt, tft

    let withValidationFeedback t : Formlet<_> =
      let t = adapt t
      F <| fun fp m d ->
        let tv, tvt, tft  = invoke t fp m d
        if isGood tft then
          tv, tvt, tft
        else
          let tes           = flatten tft
          let sb            = StringBuilder 16
          let inline app s  = sb.Append (s : string) |> ignore
          for (suppress, fp, msg) in tes do
            if not suppress then
              app msg
              app " "
          let e =
            div [|Class "invalid-feedback"|] [|str (sb.ToString ())|]
          let tvt = join tvt (ViewTree.Element e)

          tv, tvt, tft

    let withOption id lbl t : Formlet<_ option> =
      checkBox id lbl >>= (fun v -> if v then map t Some else value None)

    let withFormGroup t = Formlet.withContainer div t |> Formlet.withClass "form-group"

    let asForm extractModel onUpdate onCommit onCancel onReset (t : Formlet<'T>) : Form<'Model, 'Msg> =
      let t = adapt t
      Form <| fun m d ->
        let tv, tvt, tft  = invoke t [] (extractModel m) (D <| fun mu -> onUpdate d mu)

        let tes           = flatten tvt
        let tfs           = flatten tft
        let valid         = isGood tft
        let onCommit d    = if valid then onCommit d tv else ()
        let lis           =
          tfs
          |> Array.map (fun (s, p, m) ->
            let p   = pathToString p
            let cls = if s then "list-group-item list-group-item-warning" else "list-group-item list-group-item-danger"
            li [|Class cls|] [|str (sprintf "§ %s - %s" p m)|])
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
            [|Style [CSSProp.MarginBottom "12px"; CSSProp.MarginTop "12px"]|]
            [|
              btn onCommit "btn btn-primary" "Commit" (not valid)
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
    SocialNo        : string
    InvoiceAddress  : Address
    DeliveryAddress : Address option
  }
  static member New fn ln sno ia da =
    {
      FirstName       = fn
      LastName        = ln
      SocialNo        = sno
      InvoiceAddress  = ia
      DeliveryAddress = da
    }

open System.Text.RegularExpressions

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
    |> Bootstrap.withValidationFeedback
    |> Bootstrap.withFormGroup

  let address lbl =
    Formlet.value Address.New
    <*> input "Carry over"  ""  Validate.yes
    <*> input "Name"        ""  Validate.notEmpty
    <*> input "Street"      ""  Validate.notEmpty
    <*> input "Street"      ""  Validate.yes
    <*> input "Street"      ""  Validate.yes
    <*> input "Zip"         ""  Validate.notEmpty
    <*> input "City"        ""  Validate.notEmpty
    <*> input "County"      ""  Validate.yes
    <*> input "Country"     ""  Validate.notEmpty
    |> Bootstrap.withPanel lbl
 
  let regexSocialNo = Regex "^\d{6}-\d{5}$"

  let validateSocialNo = Validate.regex regexSocialNo "You must provide a valid Social No (DDMMYY-CCCCC)"

  let customer =
    Formlet.value Customer.New
    <*> input "First name" "Enter first name" Validate.notEmpty
    <*> input "Last name"  "Enter last name"  Validate.notEmpty
    <*> input "Social no"  "Enter social no"  validateSocialNo
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
