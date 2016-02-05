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
