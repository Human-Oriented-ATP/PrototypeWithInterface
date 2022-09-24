// Settings box logic
handleSettingsBox = function(e){
	const settings_panel = document.getElementById("settings")
	const settings_banner = document.getElementById("settings_banner")
	if(!settings_panel.contains(e.target) && !settings_banner.contains(e.target)) settings_panel.style.display = "none"
}

toggleSettings = function(){
	const settings_panel = document.getElementById("settings")
	if(settings_panel.style.display == "block"){
		settings_panel.style.display = "none"
		return;
	}
	settings_panel.style.display = "block"
}

var globalFontSize = 1

decreaseFontSize = function(){
	const rootElem = document.querySelector(":root")
	globalFontSize = Math.max(0.5, globalFontSize - 0.1)
	rootElem.style.setProperty("--box_wrapper_font_size", globalFontSize.toString() + "rem")
}

increaseFontSize = function(){
	const rootElem = document.querySelector(":root")
	globalFontSize = Math.min(2.0, globalFontSize + 0.1)
	rootElem.style.setProperty("--box_wrapper_font_size", globalFontSize.toString() + "rem")
}

