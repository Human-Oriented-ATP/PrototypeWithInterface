const getJSON = async url => {
    const response = await fetch(url);
    if(!response.ok)
      throw new Error(response.statusText);
  
    const data = response.json();
    return data;
  }

const postJSON = async (jsonToSend, url) => {
    const response = await fetch(url, {
      method: "POST",
      headers: {
        "Accept": "application/json",
        "Content-Type": "application/json"
      },
      body: JSON.stringify(jsonToSend)
    });
    if(!response.ok){
      throw new Error(response.statusText)
    }

    const data = response.json();
    return data;
}


saveProblemStateInLocalMachine = async function(){
	postJSON(globalProblemState, "http://localhost:3000/save")
}

var globalProblemState = 0;

setUpProblem = async function(){
	//const a = localStorage.getItem("problemState");
	//const b = JSON.parse(a);
	//globalProblemState = b;
	await getInitialProblemState();
	
	showProblemState();
	MathJax.typeset()
}


getInitialProblemState = async function(){
  const data = await getJSON("http://localhost:3000/teststate");
  globalProblemState = data;
}


showProblemState = function(){
  const box_wrapper = document.getElementById("box_wrapper");
  box_wrapper.innerHTML = globalProblemState.getTabHtml;
}


applyFunctionToTab = function(app){
  const actionState = {getAction: app, getProblemState: globalProblemState};
  postJSON(actionState, "http://localhost:3000/move").then(data => {
    const box_wrapper = document.getElementById("box_wrapper");
    box_wrapper.innerHTML = data.getTabHtml;

	globalProblemState = data;
	MathJax.typeset()
  }).catch(error => {
  console.error(error);
  });
}


updateExpressionLabels = function(){
	const switchElem = document.getElementById("expression_label_input");
	if(switchElem.checked){
		document.querySelector(":root").style.setProperty("--expresion_label_display", "inline");
	}
	if(!switchElem.checked){
		document.querySelector(":root").style.setProperty("--expresion_label_display", "none");
	}
}

setUpOnLoad = function(){
	setUpProblem();
	setUpManualFunctionInputListener();
	setupResizerEvents();
}


// Indicates the sequence of arguments that must be passed to the function
// 0 - hypothesis
// 1 - target
// 2 - text input
const argsToWaitForInfo = {
	"peelUniversalTarg": [1],
	"peelExistentialTarg": [1],
	"peelUniversalHyp": [0],
	"peelExistentialHyp": [0],

	"tidyImplInTarg": [1],
	"commitToHypothesis": [0],

	"tidyAndInHyp": [0],
	"tidyAndInTarg": [0],

	"tidyEverything": [],

	"modusPonens": [0,0],
	"modusPonensRaw": [0,0],

	"libEquivHyp": [2, 2, 0],
	"libEquivTarg": [2, 2, 1],

	"instantiateExistential": [2, 2]
}


var globalArgsToWaitFor = -1;
var globalArgsReceived = [];
var globalFunctionToCall = "";

resetGlobalClickState = function(){
	globalArgsToWaitFor = -1;
	globalArgsReceived = [];
	globalFunctionToCall = "";
	const hyps = document.getElementsByClassName("hyp")
	const targs = document.getElementsByClassName("targ")
	for(i=0; i<hyps.length; i++){
		let expr = hyps[i]
		expr.style.backgroundColor = "white"
	}
	for(i=0; i<targs.length; i++){
		let expr = targs[i]
		expr.style.backgroundColor = "white"
	}
}

manualFunctionInput = function(e){
	// Function which is called when the manualFunctionInput is typed in
	return;
}

setUpManualFunctionInputListener = function(){
document.getElementById("manual_function_input").addEventListener("keypress", function(e){
if (e.key == "Enter") {
	const val = e.target.value;
	e.target.value = "";
	const argsToWaitForInfoCopy = JSON.parse(JSON.stringify(argsToWaitForInfo));
	// The cost of global variables - ugly solution, but it works
	
	if(argsToWaitForInfoCopy[val] != undefined){
		globalArgsToWaitFor = argsToWaitForInfoCopy[val];
		globalArgsReceived = [];
		globalFunctionToCall = val;

		if(globalArgsToWaitFor.length == 0){
			applyFunctionToTab(globalFunctionToCall)
			resetGlobalClickState()
		}
	}
}
})}


actionButton = function(e){
	const buttonClicked = e.target.id
	const argsToWaitForInfoCopy = JSON.parse(JSON.stringify(argsToWaitForInfo));
	if(argsToWaitForInfoCopy[buttonClicked] != undefined){{
		globalArgsToWaitFor = argsToWaitForInfoCopy[buttonClicked];
		globalArgsReceived = [];
		globalFunctionToCall = buttonClicked;

		if(globalArgsToWaitFor.length == 0){
			applyFunctionToTab(globalFunctionToCall)
			resetGlobalClickState()
		}
	}
}
}


// This should only handle clicks to objects in classes which may have many instances.
// In practice, this means only hypotheses and targets
// (and possibly library related things in the future)
clickAnywhere = function(e){
	// Handle settings box (make disappear if we want it to)
	const settings_panel = document.getElementById("settings")
	if(settings_panel.style.display == "block") handleSettingsBox(e)
	console.log(e.target)
	// If we aren't expecting arguments then do nothing
	if(globalArgsToWaitFor == -1) return; 

	// And if we clicked on something that isn't a hyp/targ/button then reset the state and do nothing
	if(!e.target.classList.contains("hyp") && !e.target.classList.contains("targ")
		&& !e.target.classList.contains("action_button")){
		resetGlobalClickState()
		return;
	}
	
	const correctTypeOfExprClicked =
		((globalArgsToWaitFor[0] == 0 && e.target.classList.contains("hyp")) ||
		 (globalArgsToWaitFor[0] == 1 && e.target.classList.contains("targ")))
	const exprLoc = e.target.id

	if(!correctTypeOfExprClicked) return;

	// If we get this far, the correct type of expression was clicked, so select it
	e.target.style.backgroundColor = "#ffffcc"
	globalArgsToWaitFor.shift();
	globalArgsReceived.push(exprLoc);
	

	// Now if there are no arguments left to get, then we actually call the function.
	if(globalArgsToWaitFor.length == 0){
		const callThis = globalFunctionToCall + " " + globalArgsReceived.join(" ")
		resetGlobalClickState()
		applyFunctionToTab(callThis)
		return;
	}

}


