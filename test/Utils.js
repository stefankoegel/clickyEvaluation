"use strict";

var writer_log = [];

exports.resetLog = function(){
  writer_log = [];
};

exports.getLog = function(){
  return writer_log;
};

exports.tell = function(message){
  return function(){
    writer_log.push(message);
  };
};
