-- -*- coding: utf-8 -*-
newPackage(
	"SubalgebraBases",
	AuxiliaryFiles => true,
    	Version => "0.1",
    	Date => "November 24, 2006",
    	Authors => {{Name => "Mike Stillman",
		  Email => "mike@math.cornell.edu",
		  HomePage => "http://www.math.cornell.edu/~mike/"}},
    	Headline => "Canonical subalgebra bases (aka SAGBI/Khovanskii bases)",
	AuxiliaryFiles => true, -- set to true if package comes with auxiliary files
--  	DebuggingMode => false,
  	DebuggingMode => true		 -- set to true only during development
    	)

export {"evaluate"}
exportMutable {}

needs "./SubalgebraBases/classes.m2"
--needs "./SubalgebraBases/service-functions.m2"
--needs "./SubalgebraBases/main.m2"
--needs "./SubalgebraBases/toric_syz.m2"
--needs "./SubalgebraBases/subring_modules.m2"
--needs "./SubalgebraBases/tests.m2"

--beginDocumentation()
--needs "./SubalgebraBases/documentation.m2"

end--
