-- return the monomial order stashed inside of a ring
getMonomialOrder = R -> (options R).MonomialOrder

-- Sorts and adds the elements of the matrix "candidates" to the pending list of R
    -- R is a subalgebra
    -- candidates is a matrix of elements of the subalgebra.
    -- Algorithm makes a pass through the elements in the first row of "candidates" and places them in the correct sublist of subalgComp#"Pending".
insertPending = (R, candidates) -> (
    subalgComp := R.cache.SubalgComputations;
    
    if subalgComp#?"Pending" == false then(
	subalgComp#"Pending" = new MutableHashTable;
	);
    
    for i from 0 to (numcols candidates)-1 do(
        -- get the entry of the column and its degree
        candidate := candidates_(0,i);
        level := (degree candidate)_0;
	if subalgComp#"Pending"#?level then(
            subalgComp#"Pending"#level = append(subalgComp#"Pending"#level, candidate);
    	) else (
	    subalgComp#"Pending"#level = new MutableList from{candidate};
	);
    );
)

-- Finds the lowest nonempty list in Pending
-- Makes a pass through the lists of Pending until it finds something nonempty
    -- R is a subalgebra
    -- maxDegree is an integer
lowestDegree = (R) -> (
    subalgComp := R.cache.SubalgComputations;
    min keys subalgComp#"Pending"
    )

-- Adds newGens to R.cache.SagbiGens. Updates the appropriate rings/maps in R.cache.SubalgComputations.
    -- R is of Type Subring
    -- newGens is a 1-row matrix of generators to be added
appendToBasis = (R, newGens) -> (
    subalgComp := R.cache.SubalgComputations;
    R.cache.SagbiGens = R.cache.SagbiGens | newGens;
    R.cache.SagbiDegrees = R.cache.SagbiDegrees | flatten degrees source newGens;
    subalgComp#"PartialSagbi" = subring(R.cache.SagbiGens);
    )

--Accepts a 1-row matrix inputMatrix and returns a matrix of columns of inputMatrix whose entries all have total degree less than maxDegree
submatBelowDegree = (inputMatrix,maxDegree) -> (
    selectedCols := positions(0..numcols inputMatrix - 1,
        i -> (degrees source inputMatrix)_i < {maxDegree});
    inputMatrix_selectedCols
    )

--Accepts a 1-row matrix inputMatrix and returns a matrix of columns of inputMatrix where the highest degree entry has total degree equal to currDegree
submatByDegree = (inputMatrix, currDegree) -> (
    selectedCols := positions(0..numcols inputMatrix - 1,
        i -> (degrees source inputMatrix)_i === {currDegree});
    inputMatrix_selectedCols
    )


-- Reduces the lowest degree in subalgComp#"Pending", updating subalgComp#"Pending" and subalgComp#"sagbiGB".
-- The various maps, tensor ring, and syzygy ideal are updated to reflect this change.
-- !!!Assumes that the pending list has been subducted!!!
   -- R is the subalgebra.
   -- maxDegree is the degree limit.
processPending = (R) -> (

    subalgComp := R.cache.SubalgComputations;
    currentLowest := lowestDegree(R);
    
    if currentLowest != infinity then (
	-- remove redundant elements of the lowest degree in subalgComp#"Pending".
	reducedGenerators := gens gb(matrix{(subalgComp#"Pending")#currentLowest}, DegreeLimit=>currentLowest);
    	remove(subalgComp#"Pending", currentLowest);
    	insertPending(R, reducedGenerators);
    	-- Find the lowest degree elements after reduction.
    	currentLowest = lowestDegree(R);
	if currentLowest != infinity then (
    	    -- Add new generators to the basis
            appendToBasis(R, matrix{(subalgComp#"Pending")#currentLowest});
            remove(subalgComp#"Pending", currentLowest);
	    );
    	);
    subalgComp#"CurrentLowest" = currentLowest;
    )
)
