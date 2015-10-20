all: src/*
	psc 'src/AST.purs' 'src/Parser.purs' 'src/Evaluator.purs' 'bower_components/*/src/**/*.purs' 'bower_components/*/src/**/*.js'