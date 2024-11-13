-- Ancillary file to "p-forms from syzygies" by Alan Muniz
-- version date 17/06/2024
---------------------------

print "Companion to p-Forms from Syzygies by Alan Muniz";
---------
KD = R -> ( --module of differentials
    v:= flatten entries vars R;
    dv := apply(v, x-> value("d"|toString x));
    return R[dv,  SkewCommutative => true];
    );
--------
sing  = Forma -> ( -- compute singular ideal
    R := baseRing ring Forma;    
    saturate ideal sub( (coefficients Forma)_1, R)
    );
------------
extD = a -> ( -- exterior derivative
    S := ring a;
    R := baseRing S;
    k := (degree a)#0;
    if S_0*S_1-S_1*S_0 == 0_S then (
	    R = ring a;
	    S = KD R;
	    k = 0;
	    );
    v:= flatten entries vars R;
    dv:= flatten entries vars S;
    return (-1)^k*sum(#v, i -> diff(v_i,a)*dv_i);
    );  
----------
Hook = (campo,forma0) -> ( --compute the interior product
    S := ring forma0;
    dx := flatten entries vars S;
    n := #dx -1;
    forma := forma0;
    if instance(forma0, Matrix) then forma = forma0_0_0;
    campo1 := sub(campo, S);
    mon := flatten entries monomials forma; -- list of diff monomials appearing in forma
    final:= 0;
    for m in mon do (
	expo:= (listForm m)_0_0; -- list the exponents of m
	sgn:= 1; 
	maux:= 0;
	for l from 0 to n do (
	    if expo_l == 1 then (
		maux = maux + sub( m , {dx_l => campo1_l_0})*coefficient(m, forma)*sgn;
		sgn = -sgn;
		);
	    );
	final= final + maux;
	);
    return final
    );
--------
vec = forma -> ( --define the vector field associated  to a (n-1)-form
    S := ring forma;
    n := (rank source vars S)-1;
    eta := (extD forma);
    aux := reverse flatten entries basis({n,0},S); 
    l := apply(n+1, j-> coefficient(aux_j, eta)*(-1)^j);
    return matrix{l};
    );
------
exDiv = (d,campo) -> (
    S := ring campo;
    R := baseRing S;
    if class R === Ring then (
	    R = ring campo;
	    S = KD R;
	    );
    v := sub(campo, S);
    n := dim R -1;
    m := entries sub(basis(d,R),S);
    for j from 1 to binomial(d+n,n)-1 do (
	m = append(m, apply(last m, x-> Hook(v, extD x)));
	);
    return sub(det matrix m, R);
    );
--------
isLDS = forma0 -> ( --check whether the p-form is LDS
    S := ring forma0;
    n := (rank source vars S) -1;
    val := false;
    forma := forma0;
    if instance(forma0, Matrix) then forma = forma0_0_0;
    if forma == 0 then val = true else (
    	d := (degree forma)_0; 
    	if d <= 1 then val = true else (
            L := subsets(entries mutableIdentity(S,n+1) ,d-1);
            crit:= 0;
            for vv in L do (
            	auxf := forma;
            	for ww in vv do (
                    auxf = Hook(auxf, matrix({ww}));
            	    );
            	crit = crit + auxf*forma;
            	if  crit =!=  0 then break;   
        	);
            if crit == 0 then val = true;
    	    );
	);
    val);
----------
frms = k -> matrix applyTable(entries basis(k+1,S), x-> Hook(rad,x));
----------
Omg = (k,d,I)-> ( -- compute the generating k-forms of total degree d+k+1
    R := ring I;
    S := KD R;
    L := flatten entries(
	(matrix applyTable(entries basis(k+1,S), x-> Hook(vars R,x)))**(gens I)*matrix basis(d,I)
	);
    dg := P -> if P == 0 then 1 else sum( degree(P)); -- compute the total degree
    extDL := h ->  extD(h)/dg(h); -- weighted exterior derivative 
    sz:= (res( I, LengthLimit => (k+1) )).dd;
    forma := sub(sz_(k+1), S);
    for i from 0 to k-1 do (
    	forma = sub(sz_(k-i),S)*matrix(applyTable(entries(forma),extDL));
	);
    forma = select(flatten entries forma, x-> (degree x) == {k,d+1});
    L = L|forma;        
    return matrix{L};
    ); 
------------
rOmg = (k,d,I) -> ( -- compute random k-form of total degree d+k+1
    kk := baseRing ring I;
    om:= Omg(k,d,I);
    s := rank source om; 
    return om*random(kk^s, kk^1)
    );
------------- 
rat = (F,G) -> ( -- 1-form corresponding to a pencil 
    S := KD ring F;
    f := last degree F;
    g := last degree G;
    F0 := sub(F,S);
    G0 := sub(G,S);
    return f*F0*(extD G0) - g*G0*(extD F0);
    );
----------------
tangMod = forma0 -> ( --tangent module
    S := ring forma0;
    R := baseRing S;
    n := (rank source vars R) -1;
    forma := forma0;
    if instance(forma0, Matrix) then forma = forma0_0_0;
    k := (degree forma)_0;
    L := {};
    difb := apply( subsets(flatten entries vars S, k-1), product);
    canb := apply(entries mutableIdentity(S,n+1), x-> matrix{x});
    for v in canb do (
    	L1 := {};
    	if k>1 then (
            for w in difb do (
            	L1 = append( L1, sub(coefficient( w, Hook(v,forma)), R));
        	);
    	    )
    	else (
            L1 = append( L1, sub(Hook(v,forma), R));
    	    );
    	L = append(L,L1);
	);
    C := chainComplex(transpose matrix L, transpose vars R );
    return ( prune (HH^-1 C))
    ); 
tangSheaf = forma -> (sheaf tangMod forma)(1); --tangent sheaf
------
conMod = forma0 -> ( --conormal module
    S := ring forma0;
    R := baseRing S;
    n := (rank source vars R) -1;
    forma := forma0;
    if instance(forma, Matrix) then forma = forma_0_0;
    rad := transpose vars R;
    k := (degree forma)_0;
    L := {};
    difb := apply( subsets(flatten entries vars S, k-1), product);
    canb := apply(entries mutableIdentity(S,n+1), x-> matrix{x});
    for v in canb do (
    	L1 := {};
    	if k>1 then (
            for w in difb do (
            	L1 = append( L1, sub(coefficient( w, Hook(v,forma)), R));
        	);
    	    )
    	else (
            L1 = append( L1, sub(Hook(v,forma), R));
    	    );
    	L = append(L,L1);
	);
    return dual image transpose matrix L
    ); 
------------
conSheaf = forma -> prune (sheaf conMod forma)(-1); --conormal sheaf
------------
chern = F ->( -- Chern classes but only for rank-two sheaves
g = hilbertPolynomial(F,Projective=>false);
i := (vars ring g)_0_0;
X := coefficient(i^2,g);
Y := coefficient(i,g);
Z := coefficient(i^0,g);
return (2*X-4,  2*X^2-4*X-Y+11/3,  4/3*X^3-2*X*Y+2*Z);
);
--------------------------
rpol = (Z,d,n) -> (
    kk = baseRing ring Z;
    zz := gens Z;
    b := matrix basis(d,Z);
    r := rank source b;
    return  zz*b*random(kk^(r), kk^n);
    ); 
----
desc = C -> ( -- describe the ideal 
    pd := primaryDecomposition C;  
    pd,"codim", apply(pd, codim), "deg", apply(pd,degree)); 
----
descm = C -> ( -- describe the ideal 
    pd := primaryDecomposition C;  
    "codim", apply(pd, codim), "deg", apply(pd,degree)); 


--------------------------
loadPackage "SpaceCurves";
rand = (Z,a,b) -> (
    kk := ring Z;
    zz := gens Z;
    ma := matrix basis(a, Z); 
    mb := matrix basis(b, Z); 
    sa :=rank source ma;
    sb :=rank source mb;
    return trim ideal(zz*ma*random(kk^(sa), kk^1),zz*mb*random(kk^(sb), kk^1) );
   );
------------ make a random complete intersection (a,b)
cint = (a,b,R) -> ideal random(R^{a,b},R^1);
--- make disjoint lines
dsLns = (k,R)->  intersect apply( entries random(R^k,R^{2:-1}), ideal);  
--- make disjoint points
pts = (k,R) ->   intersect apply( entries random(R^k,R^{3:-1}), ideal);  
------------
rao = (I,mi,ma) ->( 
    L :=  toList(mi..ma);
    M := raoModule I;
    return matrix{L,apply(L, i-> hilbertFunction(i,M))};
    );
---------------
