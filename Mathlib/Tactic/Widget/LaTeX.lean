import ProofWidgets
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.SelectionPanel
import ProofWidgets.Component.GoalTypePanel

/-!

# In-progress experimentation for rendering LaTeX

This branch is for experimentation only.

We've got two ways to render math available to us:
- MathJax
- KaTeX

We put the local copies of MathJax and KaTeX at the top level. (This is not how we'd want to actually do things! Quick access for demo purposes only.)
-/

open ProofWidgets Jsx

/- Basic props -/

structure NoProps
#mkrpcenc NoProps

structure TextProps where
  text : String
#mkrpcenc TextProps

structure TeXProps extends TextProps where
  display : Bool := false
#mkrpcenc TeXProps


/- # MathJax

We switch between MathJax for SVG and MathJax for CHTML for demo purposes. That means you may need to "click to reload" at certain points—a misclick can get the webview stuck in an errored state if it tries to e.g. find a function that doesn't exist on the current MathJax object.

We have the whole MathJax *source* directory here in addition to the prebuilt MathJax, in case we want to try to modify it to get fonts to work.

To build the source in the `./mathjax` directory, run
```
cd mathjax
npm install
npm run compile
npm run make-components
cd ..
```
See [https://docs.mathjax.org/en/latest/web/hosting.html].

-/

/- ## Setting up

Here, we simply run the bundled js to get the relevant MathJax object loaded.

There are two output types we try: SVG and CommonHTML. CommonHTML fails due to access issues when looking for the fonts.

We need to check if the MathJax object already exists and, since we want to easily switch between SVG MathJax and CHTML MathJax, delete it if it does—if we try to run the bundled JS when MathJax already exists, bad things (illegal setting operations) start to happen. (In the real world we could simply not do anything instead of deleting then reloading.)

We'd presumably *not* have this as a separate component in the real worls either, but it's useful for experimenting so that the javascript of subsequent components is easier to read.
-/

/- ### SVG -/
@[widget_module]
def AddMathJaxSVG : Component NoProps where
  javascript := "
    export default function (){
      if (typeof window?.MathJax !== 'undefined') {
        delete window['MathJax']
      }" ++
      (include_str ".." / ".." / ".." / "mathjax-prebuilt" / "es5" / "tex-svg.js") ++ "
    }"

/- ### CommonHTML -/
@[widget_module]
def AddMathJaxCHTML : Component NoProps where
  javascript := "
    export default function (){
      if (typeof window?.MathJax !== 'undefined') {
        delete window['MathJax']
      }" ++
      (include_str ".." / ".." / ".." / "mathjax-prebuilt" / "es5" / "tex-chtml.js") ++ "
    }"

/- ## Rendering

There are three ways to render typesetting in MathJax: with `MathJax.typeset()`, `MathJax.typesetPromise()`, and by producing HTMLElements with converters.

-/

/- ### Using converters

There are probably better ways to use an HTMLElement than via `dangerouslySetInnerHTML`, but it at least lets us see some math! I'm going to look into using a ref next.
-/

/- __SVG via dangerouslySetInnerHTML__
Hacky but works just fine in this limited context. Proof-of-concept.
-/
@[widget_module]
def DangerousMathJaxSVG : Component TeXProps where
  javascript := "
    import * as React from 'react'
    export default function(props) {
      if (typeof window?.MathJax !== 'undefined') {
        const html = window.MathJax.tex2svg(props.text, {display:props.display}).outerHTML
        return React.createElement('span', {dangerouslySetInnerHTML:{__html:html}}) }}"

#html <AddMathJaxSVG /> -- evaluate first
#html <DangerousMathJaxSVG text="\\int_0^\\infty t^{z-1}e^{-t}\\;dt" display={true} />

/- __CHTML via dangerouslySetInnerHTML__
Fails! Can't get the fonts; from the webview inspector:
```
GET vscode-webview://../es5/output/chtml/fonts/woff-v2/MathJax_Math-Italic.woff net::ERR_ACCESS_DENIED
```
This seems related to (this vscode issue)[https://github.com/microsoft/vscode/issues/102959].
This suggests we could use `panel.webview.asWebviewUri(vscode.Uri.file(...))` in front of(?) the value of `fontURL` in `./mathjax/components/src/output/chtml/fonts/tex/tex.js`, but I couldn't get the `vscode` npm dependency to work.
-/
@[widget_module]
def DangerousMathJaxCHTML : Component TeXProps where
  javascript := "
    import * as React from 'react'
    export default function(props) {
      if (typeof window?.MathJax !== 'undefined') {
        const html = window.MathJax.tex2chtml(props.text, {display:props.display}).outerHTML
        return React.createElement('span', {dangerouslySetInnerHTML:{__html:html}}) }}"

#html <AddMathJaxCHTML /> -- evaluate first
-- fails; no fonts. (Blank.)
#html <DangerousMathJaxCHTML text="\\int_0^\\infty t^{z-1}e^{-t}\\;dt" display={true} />

/- # KaTeX

We fork KaTeX so that we can inline fonts via `webpack`.
With the changes made in this KaTeX fork, we can now write
```
cd KaTeX
yarn install
USE_TTF=false USE_WOFF=false BUNDLE_FONTS=true yarn build
```
This means that we only use the `*.woff2` fonts, and we inline them into the generated css files.

We need to check that woff2 is appropriate in all places (e.g. vscode for web?) given that it's the most modern format.

Honestly, I'd prefer to simply link to the (normal) CSS via vscode resource URI. But that's quite difficult. We at least need to obtain the workspace folder, and preferably use the standard means to generate a vscode resource URI instead of hacking one together. But all that functionality comes from the `vscode` JS API, which is not accessible at the point the javascript gets run (nor anywhere else). It'd be great to expose this somehow, but in the meantime, we can bundle.
-/

