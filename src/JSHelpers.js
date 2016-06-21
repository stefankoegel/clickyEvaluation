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

exports.ctrlKeyPressed = function(event) {
     return (!!(event.ctrlKey || event.metaKey))
};

exports.getType = function(event) {
  return event.type;
}

exports.showTooltip = function(div) {
  return function(outer){
    return function(e){
      return function(){
        var out = outer[0];
        var d = div[0];

        function timeoutFunc(e){
          var posX = e.pageX + 10;
          var posY = e.pageY + 10;
          out.style.top = posY + "px";
          out.style.left = posX + "px";
          out.style.visibility = "visible";
        }

        var delayTime = 200;

        var delay = setTimeout(function () {timeoutFunc(e)},delayTime);

        d.onmousemove = function(e){
          e.stopPropagation();
          clearTimeout(delay);
          delay = setTimeout(function () {timeoutFunc(e)},delayTime);
        }

        d.onmouseout = function(e){
          e.stopPropagation();
          out.style.visibility = "hidden";
          clearTimeout(delay);
        }
      }
    };
  };
};


exports.children = function(selector) {
    return function(ob) {
        return function() {
            return ob.children(selector);
        };
    };
};

exports.prepend = function(child) {
  return function(parent) {
    return function() {
      return parent.prepend(child);
    }
  }
}

exports.warnOnRefresh = function() {
  window.onbeforeunload = function() {
    return "Your changes in the Definitions will be lost when you leave or refresh! Are you sure?";
  };
  return {};
};

exports.showTypes = function(){
  $('#typecheckbox').bootstrapSwitch('state', true);
  return {};
};
