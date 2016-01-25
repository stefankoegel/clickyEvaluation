/* global exports */
"use strict";

// module JSHelpers

exports.jqMap = function(func) {
    return function(ob) {
        return function() {
            ob.map( function(i, e) { return func(jQuery(e))(); } );
        };
    };
};

exports.isEnterKey = function(event) {
    return event.which == 13;
};

// creates Canvas and return
// canvas already in html side
exports.createCanvas = function(){
  var svgContainer = document.getElementById("svg-container");
  while (svgContainer.hasChildNodes()) {
    svgContainer.removeChild(svgContainer.lastChild);
  }
  var outContainer = document.getElementById("topLevelOutput-container");
  var canvas = Raphael(svgContainer,$(outContainer).width(),$(outContainer).height());
  svgContainer.style.top = $(outContainer).position().top + "px"
  return canvas
}
