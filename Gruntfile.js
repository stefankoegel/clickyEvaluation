module.exports = function(grunt) {

  "use strict";

  grunt.initConfig({

    srcFiles: ["src/**/*.purs", "bower_components/**/src/**/*.purs"],

    psc: {
      options: {
        modules: ["StateEffect"],
        main: ["StateEffect"]
      },
      all: {
        src: ["<%=srcFiles%>"],
        dest: "html/dist/Main.js"
      }
    },

    dotPsci: ["<%=srcFiles%>"],

    testEff: {
      options: {
        modules: ["StateEffect"]
      },
      all: {
        src: ["<%=srcFiles%>"],
        dest: "dist/Test.js"
      }
    }
  });

  grunt.loadNpmTasks("grunt-purescript");
  grunt.registerTask("default", ["psc:all", "dotPsci"]);
};
