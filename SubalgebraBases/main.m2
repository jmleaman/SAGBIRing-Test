debug Core -- gets rid of "raw" error during installation. probably a better way...

export {
    "subduction",
    "subalgebraBasis",
    "sagbi",
    "PrintLevel",
    "SagbiDegrees",
    "SubalgComputations",
    "SagbiGens",
    "SagbiDone",
    "appendToBasis" -- temporary
    }




-- Performs subduction using the generators of subR.
-- currently does not require the generators to be a Sagbi basis.
subduction = method(TypicalValue => RingElement)
subduction(Subring, RingElement) := (S, f) -> (
    pres := S.cache.SAGBIComputations#"SAGBIData"#"SAGBIPresRing";
    tense := pres#"TensorRing";
    if ring f === tense then (
	f = (pres#"FullSubstitution")(f);
	)else if ring f =!= ambient S then (
	error "f must be from the (ambient subR) or subR's TensorRing.";
	);
        
    -- It is possible for ring f === ambient to be true but f is still from a different ring 
    -- than pres#"TensorRing". In this case, it shouldn't try to prevent an error by using "sub"
    -- or something. Instead, the following line will deliberately throw an error:
    -- (This is done because otherwise there is potential for a segfault.)
    throwError := f - 1_(ambient S);   
    
    if not S.cache#?"SyzygyIdealGB" then (
	S.cache#"SyzygyIdealGB" = gb (pres#"SyzygyIdeal");
	);
    J := subR.cache#"SyzygyIdealGB";
        
    F := pres#"Substitution";
    numblocks := rawMonoidNumberOfBlocks raw monoid ambient subR;
    fMat := matrix({{pres#"InclusionAmbient"(f)}});    
    result := rawSubduction(numblocks, raw fMat, raw F, raw J);
    result = promote(result_(0,0), tense);
    result
    );

-- The C++ implementation of rawSubduction could be improved.
-- Here is the code path that it takes:
-- (M2) subduction(Matrix) -> (M2) subduction(RingElement) -> (C++) rawSubduction(Matrix) -> (C++) subduction(RingElement)
-- If we deleted the C++ rawSubduction(Matrix) function and made rawSubduction take a RingElement, we could have:
-- (M2) subduction(Matrix) -> (M2) subduction(RingElement) -> (C++) subduction(RingElement)
subduction(Subring, Matrix) := (subR, M) -> (	
    ents := for i from 0 to (numcols M)-1 list(
    	subduction(subR, M_(0,i))
	);
    matrix({ents})
    );

---------------------------------------------------------------------------------------
-- subalgebraBasis is needed for legacy purposes. It should not be changed or deleted. 
-- New code should use the function "sagbi." 
---------------------------------------------------------------------------------------

subalgebraBasis = method(
    TypicalValue => Matrix, 
    Options => {
	Strategy => null,
    	Limit => 100,
    	PrintLevel => 0
	}
    );

subalgebraBasis(Matrix) := opts -> gensMatrix -> (
    R := subring gensMatrix;
    gens sagbi(R,opts)
    );

subalgebraBasis(List) := opts -> L -> (
    gens sagbi(opts, subring L)
    );

subalgebraBasis(Subring) := opts -> subR -> (
    gens sagbi subR
    );


sagbi = method(
    TypicalValue => Subring, 
    Options => {
    	Strategy => null,
    	Limit => 100,
    	PrintLevel => 0
    	}
    );

sagbi(Matrix) := opts -> gensMatrix -> (
    sagbi(opts, subring gensMatrix)
    );

sagbi(List) := opts -> L -> (
    sagbi(opts, subring L)
    );

sagbi(Subring) := opts -> S -> (
    
    R := ambient S;
    
    
    -- previously named S.cache.SubalgComputations
    S.cache#"SAGBIComputations" = new MutableHashTable;
    
    -- change subalgCopm to SAGBIComp in other functions!
    SAGBIComp := S.cache#"SAGBIComputations";
    
    if #(S#"SAGBIData") == 0 then (
	    SAGBIComp#"SAGBIGens" = matrix(ambient S,{{}});
	    SAGBIComp#"SAGBILimit" = opts.Limit;
	    SAGBIComp#"SAGBIDegree" = null;
	    --SAGBIMaximum is from old code; may be needed in later updates
	    SAGBIComp#"SAGBIMaximum" = (max degrees source gens S)_0;
	    SAGBIComp#"SAGBIDegs" = {};
	    SAGBIComp#"SAGBIDone" = false;
	    SAGBIComp#"SAGBIPresRing" = null;
	    -- error occurs if SAGBIPresRing is constructed by makePresRing with an empty list;
	    SAGBIComp#"SAGBIPending" = new MutableHashTable;
	) else if S#"SAGBIData"#"SAGBIDone" then (
	    return S;
	) else (
	    SAGBIComp#"SAGBIGens" = S#"SAGBIData"#"SAGBIGens";
	    SAGBIComp#"SAGBILimit" = opts.Limit;
	    SAGBIComp#"SAGBIDegree" = S#"SAGBIData"#"SAGBIComputations"#"SAGBIDegree";
	    --SAGBIMaximum is from old code; may be needed in later updates
	    SAGBIComp#"SAGBIMaximum" = S#"SAGBIData"#"SAGBIComputations"#"SAGBIMaximum";
	    SAGBIComp#"SAGBIDegs" = S#"SAGBIData"#"SAGBIDegs";
	    SAGBIComp#"SAGBIDone" = S#"SAGBIData"#"SAGBIDone";
	    SAGBIComp#"SAGBIPresRing" = S#"SAGBIData"#"SAGBIPresRing";
	    SAGBIComp#"SAGBIPending" = S#"SAGBIData"#"SAGBIHash"#"SAGBIPending";
	);
    
    
    SAGBIComp#"SAGBIgb" = null;
    syzygyPairs := null;
    newPending := null;
    
    return;
-- This is where we left off!

    -- Get the maximum degree of the generators. This is used as a stopping condition.

    -- Only look at generators below degree limit.  Add those generators to the SubalgebraGenerators
    reducedGens := compress submatBelowDegree(gens S, opts.Limit+1);
    insertPending(S, reducedGens, opts.Limit);
    -- Remove elements of coefficient ring
    (subalgComp#"Pending")#0 = {};
    processPending(S, opts.Limit);
    
    SAGBIComp#"SAGBIDegree" = SAGBIComp#"CurrentLowest" + 1;
       
    while SAGBIComp#"SAGBIDegree" <= opts.Limit and not SAGBIComp#"SAGBIDone" do (  	
	
	partialSagbi := SAGBIComp#"SAGBIPresRing";
	pres := partialSagbi#"PresRing";

	-- SyzygyIdeal is A_I in Sturmfels chapter 11.
	partialSagbi.cache#"SyzygyIdealGB" = gb(pres#"SyzygyIdeal", DegreeLimit => currDegree);
	sagbiGB := partialSagbi.cache#"SyzygyIdealGB";
	
	-- This will select the entries of partialSagbi.cache#"SyzygyIdealGB" that do not involve any of (leadTerms subalgComp#"SyzygyIdeal") and 
	-- also have degree equal to currDegree. So, they will be exclusively in the higher block of variables of TensorRing.
	zeroGens := submatByDegree(mingens ideal selectInSubring(1, gens sagbiGB), currDegree);
	
	-- Plug the generators into the degree currDegree polynomials that eliminate the lead terms (I.e. zeroGens.) 
	-- This changes it from a polynomial in the generators to a polynomial in the variables of the ambient ring.
       	syzygyPairs = pres#"Substitution"(zeroGens);

	-- Have we previously found any syzygies of degree currDegree?
        if subalgComp#"Pending"#currDegree != {} then (
            syzygyPairs = syzygyPairs | pres#"InclusionBase"(matrix{subalgComp#"Pending"#currDegree});
            subalgComp#"Pending"#currDegree = {};
            );
	
       	subd := subduction(partialSagbi, syzygyPairs);
	
       	if entries subd != {{}} then (
	    -- converts back to the variables of the ambient ring.
	    subducted := (pres#"ProjectionBase")(subd);
	    newElems = compress subducted;
            ) else (
	    newElems = subd;
	    );
	
	if numcols newElems > 0 then (
	    -- Put newElems in pending and update subalgComp. 
            insertPending(R, newElems, o.Limit);
    	    processPending(R, o.Limit);
	    currDegree = subalgComp#"CurrentLowest";
            ) else (
	    -- "rawStatus1 raw (subalgComp#"sagbiGB") == 6" means that the GB is a complete GB (as if DegreeLimit was not specified.)
	    if sum toList apply(subalgComp#"Pending", i -> #i) == 0 and rawStatus1 raw sagbiGB == 6 and currDegree > maxGensDeg then (
                R.cache.SagbiDone = true;
                if (o.PrintLevel > 0) then (
		    print("Finite SAGBI basis was found.");
		    );
            	);
            );
	currDegree = currDegree + 1;
    	);
    
    if currDegree > o.Limit then(
	isPartial = true;
	);
    -- Possibly, it could finish on the same run that it successfully terminates.
    if R.cache.SagbiDone == true then(
	isPartial = false;
	);
    
    if currDegree > o.Limit and o.PrintLevel > 0 then (
	print("Limit was reached before a finite SAGBI basis was found.");
    	);    

    -- We return a new instance of subring instead of the generators themselves so that we can say whether or not a Subring instance
    -- IS a Sagbi basis, not whether or not it HAS a Sagbi basis. (The latter is unacceptable because the cache should not effect 
    -- the value of a function.)
        
    -- If subalgebraBasis is called on a Subring instance with a previously computed Sagbi basis that is not itself a Sagbi basis,
    -- a new subring instance will be constructed from its cached SagbiGens. This is OK because different instances of the same 
    -- subring will still be equal if we calculate equality based on the mathematical equality of the subalgebras they generate.
    -----------------------------------------------------------------------------------------------------
    -- subR.cache.SagbiDone: Indicates whether or not the Subring instance has a cached Sagbi basis. 
    -- subR.isSagbi        : Indicates whether or not (gens subR) itself is a Sagbi basis.
    -----------------------------------------------------------------------------------------------------
    -- The correct way to implement a function that requires a Subring instance that is a Sagbi basis is to check that 
    -- (subR.isSagbi == true). If (subR.isSagbi == false) and (subR.cache.SagbiDone == true), an error should still be thrown.
    
    
    resultR := ambient R;
    M := R.cache.SagbiGens;
    presRing := makePresRing(resultR, M);
    
    -- It shouldn't directly set (cache => R.cache) because there is a possibility of inhereting outdated information. 
    cTable := new CacheTable from{
	SubalgComputations => new MutableHashTable from {},
	SagbiGens => M,
	SagbiDegrees => R.cache.SagbiDegrees,
	SagbiDone => R.cache.SagbiDone
	}; 
    new Subring from {
    	"AmbientRing" => resultR,
    	"Generators" => M,
	"PresRing" => presRing,
    	"isSagbi" => R.cache.SagbiDone,
	"isPartialSagbi" => isPartial,
	"partialDegree" => currDegree-1,
	cache => cTable
	} 
    );
