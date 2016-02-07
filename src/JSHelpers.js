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
          event.stopPropagation();
          clearTimeout(delay);
          delay = setTimeout(function () {timeoutFunc(e)},delayTime);
        }

        d.onmouseout = function(){
          event.stopPropagation();
          out.style.visibility = "hidden";
          clearTimeout(delay);
        }
      }
    };
  };
};
