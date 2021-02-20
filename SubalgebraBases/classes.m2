-- This is for testing new features

export {
    "Subring",
    "subring",
    "PresRing",
    "makePresRing",
    "getWeight",
    "setWeight",
    "presentationRing",
    "VarBaseName",
    "recordsagbi",
    "sagbidone",
    "sagbigens",
    "sagbiring",
    "storePending",
    "limit",
    "SAGBIBasis",
    "sagbiBasis"
}

-- Subring data type
-- A subring is meant to be fairly light-weight.
-- Subrings include the ambient ring, their generators
-- a boolean indicating whether the generators are SAGBI and
-- a PresRing (see later)

Subring = new Type of HashTable

subring = method(Options => true)
subring Matrix := {} >> opts -> M -> (
    new Subring from{
        "ambientRing" => ring M,
        "generators" => M,
        "presentation" => makePresRing(opts, ring M, M),
        "isSAGBI" => false,
        cache => new CacheTable from {}
    }
)
subring List := {} >> opts -> L -> subring(opts, matrix{L})

-- Subring access functions

ambient Subring := A -> A#"ambientRing"
gens Subring := o -> A -> A#"generators"

-- SAGBIBasis data type
-- This is a computation object which can hold the intermediate
-- results of a sagbi basis computation.
-- This is similar to the output of a gb calculation

SAGBIBasis = new Type of HashTable

sagbiBasis = method(Options => true)
sagbiBasis Subring := {limit => 100} >> opts -> S -> (
    stopping := new HashTable from {"limit" => opts.limit, "degree" => -1, "maximum" => -1};
    pending := new HashTable;
    new SAGBIBasis from {
        "ambientRing" => ambient S,
        "subringGenerators" => gens S,
        "sagbiGenerators" => matrix(ambient S,{{}}),
        cache => new CacheTable from {},
        "sagbiDegrees" => matrix(ZZ,{{}}),
        "sagbiDone" => false,
        "stoppingData" => stopping,
        "pending" => pending,
        "presentation" => null
    }
)

sagbiBasis (Subring, MutableHashTable) := {storePending => true} >> opts -> (S,H) -> (
    stopping := new HashTable from {"limit" => H#"limit", "degree" => H#"degree", "maximum" => H#"maximum"};
    pending := if opts.storePending then new HashTable from H#"pending" else new HashTable;
    new SAGBIBasis from {
        "ambientRing" => ambient S,
        "subringGenerators" => gens S,
        "sagbiGenerators" => H#"gens",
        cache => new CacheTable from {},
        "sagbiDegrees" => H#"degs",
        "sagbiDone" => H#"done",
        "stoppingData" => stopping,
        "pending" => pending,
        "presentation" => makePresRing(opts, ambient S, H#"gens")
    }
)

subring SAGBIBasis := {} >> opts -> S -> (
    if #flatten entries S#"sagbiGenerators" == 0 then subring S#"subringGenerators"
    else if S#"sagbiDone" then new Subring from{
        "ambientRing" => ring S#"sagbiGenerators",
        "generators" => S#"sagbiGenerators",
        "presentation" => makePresRing(opts, ring S#"sagbiGenerators", S#"sagbiGenerators"),
        "isSAGBI" => true,
        cache => new CacheTable from {}
    }
    else (
        << "This is not implemented yet, subduction should be invoked";
        subring (S#"subringGenerators" | S#"sagbiGenerators")
        )
)

-- This type is compatible with internal maps that are generated in the Sagbi algorithm.
-- Originally, this was stored directly in the cache of an instance of Subring.
-- The problem with that solution is there is a need to use these maps outside of the Sagbi algorithm computations.
-- Also, the cache should not be used in a way that causes side effects.
PresRing = new Type of HashTable

net PresRing := pres -> (
tense := pres#"TensorRing";
A := numcols vars tense;
B := numcols selectInSubring(1, vars tense);
"PresRing instance ("|toString(B)|" generators in "|toString(A-B)|" variables)"
)

-- gensR are elements of R generating some subalgebra.
-- R is a polynomial ring.
makePresRing = method(TypicalValue => PresRing, Options => {VarBaseName => "p"})
makePresRing(Ring, Matrix) := opts -> (R, gensR) -> (
if(R =!= ring(gensR)) then(
error "The generators of the subalgebra must be in the ring R.";
);
makePresRing(opts, R, first entries gensR)
);

makePresRing(Ring, List) := opts -> (R, gensR) ->(
gensR = sort gensR;

if #gensR == 0 then(
error "List passed to makePresRing must not be empty.";
);

if(ring(matrix({gensR})) =!= R) then(
error "The generators of the subalgebra must be in the ring R.";
);

ambR := R;
nBaseGens := numgens ambR;
nSubalgGens := length gensR;

-- Create a ring with combined generators of base and subalgebra.
MonoidAmbient := monoid ambR;
CoeffField := coefficientRing ambR;

-- Construct the monoid of a ring with variables corresponding to generators of the ambient ring and the subalgebra.
-- Has an elimination order that eliminates the generators of the ambient ring.
-- The degrees of generators are set so that the SyzygyIdeal is homogeneous.
newOrder := prepend(Eliminate nBaseGens, MonoidAmbient.Options.MonomialOrder);

NewVariables := monoid[
VariableBaseName=> opts.VarBaseName,
Variables=>nBaseGens+nSubalgGens,
Degrees=>join(degrees source vars ambR, degrees source matrix({gensR})),
MonomialOrder => newOrder];

TensorRing := CoeffField NewVariables;

ProjectionInclusion := map(TensorRing, TensorRing,
(matrix {toList(nBaseGens:0_(TensorRing))}) |
(vars TensorRing)_{nBaseGens .. nBaseGens+nSubalgGens-1});

ProjectionAmbient := map(ambR, TensorRing,
(vars ambR) | matrix {toList(nSubalgGens:0_(ambR))});

InclusionAmbient := map(TensorRing, ambR,
(vars TensorRing)_{0..nBaseGens-1});

Substitution := map(TensorRing, TensorRing,
(vars TensorRing)_{0..nBaseGens-1} | InclusionAmbient(matrix({gensR})));

genVars := (vars TensorRing)_{numgens ambient R..numgens TensorRing-1};

SyzygyIdeal := ideal(genVars - InclusionAmbient(leadTerm matrix({gensR})));

liftedPres := ideal(Substitution(genVars) - genVars);
FullSubstitution := ProjectionAmbient*Substitution;

ht := new HashTable from {
"TensorRing" => TensorRing,
"ProjectionInclusion" => ProjectionInclusion,
"ProjectionAmbient" => ProjectionAmbient,
"InclusionAmbient" => InclusionAmbient,
"Substitution" => Substitution,
"FullSubstitution" => FullSubstitution,
"SyzygyIdeal" => SyzygyIdeal,
"LiftedPres" => liftedPres
};

new PresRing from ht
);

-- The reason why this is implemented is to prevent incorrect usage of the makePresRing constructor.
-- A subring is already associated with an immutable PresRing instance which should be used instead of
-- constructing a new instance. Don't use makePresRing when you can use the function subring.
makePresRing(Subring) := opts -> subR -> (
subR#"PresRing"
);

end---Michael


subring = method(Options => {VarBaseName => "p"})
subring Matrix := opts -> M -> (
    R := ring M;
    cTable := new CacheTable from{};
    SAGBIData := new HashTable from{};
    new Subring from {
    	"AmbientRing" => R,
    	"Generators" => M,
	-- The PresRing of a Subring instance is immutable because the generators are immutable.
	"PresRing" => makePresRing(opts, R, M),
	cache => cTable,
	-- If this is empty, then no SAGBI computation has been computed.
	-- If this is nonempty, then SAGBI has started.
	-- The SAGBI computation is complete if SAGBI_Done is true
	"SAGBIData" => SAGBIData
	}
    )
subring List := opts -> L -> subring(opts, matrix{L})

storesagbi = method(Options => {storePending => true})
storesagbi Subring := opts -> S -> (
    R := ambient S;
    M := gens S;
    cTable := new CacheTable from{};
    if S.cache#?"SAGBIComputations" then (
    	SAGBIComp := S.cache#"SAGBIComputations",
	Gens := SAGBIComp#"SAGBIGens",
	SAGBIHash := new HashTable from{
	    "SAGBILimit" => SAGBIComp#"SAGBILimit",
	    "SAGBIDegree" => SAGBIComp#"SAGBIDegree",
	    "SAGBIMaximum" => SAGBIComp#"SAGBIMaximum",
	    if opts.storePending then (
		"SAGBIPending" => SAGBIComp#"Pending";
		) else (
		"SAGBIPending" => new MutableHashTable;
		)
	    };
	SAGBIData := new HashTable from{
	    "SAGBIGens" => Gens,
	    "SAGBIDegs" => SAGBIComp#"SAGBIDegs",
	    "SAGBIDone" => SAGBIComp#"SAGBIDone",
    	    "SAGBIComputations" => SAGBIHash,
	    "SAGBIPresRing" => makePresRing(opts, R, Gens)
	    };
    	new Subring from{
	    "AmbientRing" => R,
	    "Generators" => M,
	    "PresRing" => makePresRing(opts, R, M),
	    cache => cTable,
	    "SAGBIData" => SAGBIData
    	    }
    	) else (
	    subring M	
    	)
    )

sagbidone = method(Options => {})
sagbidone Subring := opts -> S -> (
    	if #(S#"SAGBIData") == 0 then false
	else S#"SAGBIData"#"SAGBIDone"
    )
 
gens Subring := o -> A -> A#"Generators"
numgens Subring := A -> numcols gens A
ambient Subring := A -> A#"AmbientRing"
net Subring := A -> "subring of " | toString(ambient A)

sagbigens = method(
    TypicalValue => Subring,
    Options=>{
	Strategy => null,
    	Limit => 100,
    	PrintLevel => 0
	}
    )
sagbigens Subring := opts -> S -> (
    	if #(S#"SAGBIData") == 0 then subalgebraBasis(S, opts)
	else if opts.Limit > S#"SAGBIData"#"SAGBIComputations"#"SAGBILimit" then subalgebraBasis(S, opts)
	else if sagbidone S then S#"SAGBIData"S"SAGBIGens"
	else (
	    S#"SAGBIData"S"SAGBIGens" | subduction(subring gens S, S#"SAGBIData"#"SAGBIGens")
	    ) 
    )

sagbiring = method(
    TypicalValue => Subring,
    Options=>{
	Strategy => null,
    	Limit => 100,
    	PrintLevel => 0
	}
    )
sagbiring Subring := opts -> S -> (
    	subring sagbigens(opts, S)
    )

end--

-- Returns the tensor ring because the function ambient returns the ambient ring.
ring Subring := A -> (
    A#"PresRing"#"TensorRing"
    );

-- f % Subring is never going to be an element of the subalgebra, hence the ouput
-- is in the lower variables of TensorRing.
-- input: f in ambient A or TensorRing of A. 
-- output: r in TensorRing of A such that f = a + r w/ a in A, r "minimal"
RingElement % Subring := (f, A) -> (
    pres := A#"PresRing";
    if ring f === ambient A then(
	f = (pres#"InclusionBase")(f);
	) else if ring f =!= pres#"TensorRing" then(
	error "The RingElement f must be in either TensorRing or ambient A.";
	);
    ans := (subduction(A, f));
    ans    
    );

-- f // Subring is always going to be inside of the subalgebra, hence the output
-- should be in the upper variables of TensorRing. 
-- NOTE: If you want to compute FullSub(f//A), it is a lot faster to compute f-(f%A).
-- input: f in ambient A or TensorRing of A. 
-- output: a in TensorRing of A such that f = a + r w/ a in A, r "minimal."
RingElement // Subring := (f, A) -> (
    pres := A#"PresRing";
    tense := pres#"TensorRing";
    if ring f === ambient A then(
	f = (pres#"InclusionBase")(f);
	) else if ring f =!= tense then(
	error "The RingElement f must be in either the TensorRing or ambient ring of A.";
	);
    result := f - (f % A);
    I := pres#"LiftedPres";
    result % I
    );

-- Sends each entry e to e%A
Matrix % Subring := (M, A) -> (
    pres := A#"PresRing";
    ents := for i from 0 to numrows M - 1 list(
	for j from 0 to numcols M - 1 list(M_(i,j) % A)
	);
    matrix(pres#"TensorRing", ents)
    );

-- Sends each entry e to e//A
Matrix // Subring := (M, A) -> (
    pres := A#"PresRing";
    ents := for i from 0 to numrows M - 1 list(
	for j from 0 to numcols M - 1 list(M_(i,j) // A)
	);
    matrix(pres#"TensorRing", ents)
    );

-- Perhaps it is a bug that this will sometimes throw an error when it should return false
member (RingElement, Subring) := (f, A) -> (
    r := f%A;
    r == 0_(A#"PresRing"#"TensorRing")
    );





-----------------------------------------------------------------
-- experimental valuation type
-----------------------------------------------------------------

Valuation = new Type of HashTable
-- what should a valuation need to know?
source Valuation := v -> v#source
target Valuation := v -> v#target
net Valuation := v -> "valuation: " | toString target v | " <-- " | toString source v
Valuation RingElement := (v, f) -> (
    assert(v#?evaluate and ring f === source v);
    assert instance(v#evaluate, Function);
    v#evaluate f
    )

MonomialValuation = new Type of Valuation
monomialValuation = method()
monomialValuation Ring := R -> new MonomialValuation from {
    source => R,
    target => ZZ^(numgens R),
    evaluate => (f -> matrix exponents leadTerm f)
    }
leadTerm (MonomialValuation, RingElement) := (v, f) -> (
    assert(ring f === source v);
    leadTerm f
    )


-- set a weight on the ambient ring that induces a weight on the presentation ring
setWeight = method()
setWeight (Subring, List) := (A, W) -> (
    B := ambient A;
    assert(numgens B == length W);
    if not A.cache#?"AmbientWeight" then (
	A.cache#"AmbientWeight" = W;
	) else (
	print "Weight has already been set"
	);
    )

getWeight = method()
getWeight Subring := A -> (
    if not A.cache#?"AmbientWeight" then (
	return "None set"
	);
    A.cache#"AmbientWeight"
    )


-*
R=QQ[x,y]
f = x+y^2
v = monomialValuation R
source v
target v
v f
leadTerm(v,f) < y
*-

end--
