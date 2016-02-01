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
    svgContainer.style.top = "-" + $(outContainer).outerHeight() + "px";
    var canvas = Raphael(svgContainer,$(outContainer).width(),$(outContainer).height());
    return canvas;
};

exports.offsetTop = function(ob){
  return function(){
    return $(ob).offset().top;
  };
};

exports.offsetLeft = function(ob){
  return function(){
    return $(ob).offset().left;
  };
};

exports.outerHeight = function(ob){
  return function(){
    return $(ob).outerHeight();
  };
};

exports.outerWidth = function(ob){
  return function(){
    return $(ob).outerWidth();
  };
};

exports.path = function(canvas) {
  return function(str){
    return function (){
      canvas.path(str);
    };
  };
};
