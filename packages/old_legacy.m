/* vim: set syntax=magma : */
/*
    We store here the intrinsics that have been superseeded.
*/

intrinsic LoadPPAVs(label, directory : prec := 100) -> SeqEnum
{ loads precomputed PPAVs in an isogeny class }
    recs := getrecs(directory cat "/av_fq_pol_output/" cat label);
    g, q, f := LabelToPoly(label);

    R := LoadSchemaWKClasses(Read(directory cat "/wk_classes/" cat label cat "_schema.txt"));
    reps_isom, _ := ICM_DistinguishedRepresentatives(R);
    isom_labels := [label cat "." cat r`IsomLabel : r in reps_isom];

    A := Algebra(reps_isom[1]);
    F:=PrimitiveElement(A);
    V:=q/F;
    basis:=[ V^i : i in [g-1..0 by -1]] cat [F^i : i in [1..g]];
    zb_in_A:=function(jsonb)
        rep := Split(jsonb, ",[]");
        den := atoi(rep[1]);
        nums := atoii(Sprint(rep[2..#rep]));
        return SumOfProducts([c/den : c in nums], basis);
    end function;

    reps_pp := [zb_in_A(rec[10]) : rec in recs];

    res := [<reps_isom[Index(isom_labels, recs[i][1])], elt> : i->elt in reps_pp];;


    // checks polarization sends I to its dual TraceDual Complex conjugate
    assert forall{ x0*I eq TraceDualIdeal(ComplexConjugate(I)) where I, x0 := Explode(elt) : elt in res};

    pps_by_isom := AssociativeArray();
    for label in isom_labels do
        pps_by_isom[label] := [];
    end for;
    // check that the ratio with any other is totally positive
    for elt in res do
        label := elt[1]`IsomLabel;
        b, v := IsDefined(pps_by_isom, label);
        if not b then
            pps_by_isom[label] := [];
            v := pps_by_isom[label];
        end if;
        Append(~v, elt[2]);
        // assert that it is purely imaginary
        assert elt[2] eq -ComplexConjugate(elt[2]);
    end for;
    homs := HomsToC(A : Prec:=prec);
    CC := ComplexFieldExtra(prec);
    for v in pps_by_isom do
        assert forall{
            Real(qCC) gt 0 and Imaginary(qCC) lt CC`epscomp where qCC := CC!h(q)
            : h in homs, q in quotients}
             where quotients := [elt1/elt2 : i->elt1 in v, j->elt2 in v | i gt j];
    end for;
    return res;
end intrinsic;

intrinsic PeriodMatricesDistinguishedLift(label, directory, prec) -> SeqEnum, SeqEnum
{ returns the period matrices associated to PPAVs in a isogeny class, by loading precomputed data, see LoadPPAVS }
    CC := ComplexFieldExtra(prec);
    ppavs := LoadPPAVs(label, directory);
    A := Algebra(ppavs[1,1]);
    fields, _, _ := Components(A);
    PHI := CMType(ppavs[1,2]);
    ChangePrecision(~PHI, Ceiling(prec*1.2)+100);
    res := [
        <elt[1], elt[2], Matrix(CC, bigP), Matrix(CC, t)>
        where bigP, t := PeriodMatrix(elt[1], elt[2], PHI)
        : elt in ppavs];
    return res, fields;
end intrinsic;


intrinsic PrincipalPolarizationsIsogenyClass(R::AlgEtQOrd)->SeqEnum
{Returns a sequence of tuples < I, [x1,...,xn] > where (I,x1),...,(I,xn) represent the isomorphism classes of PPAVs corresponding with underlying AV given by I. Ideally, R=Z[F,V]. Important: isomorphism classes without a principal polarization are not returned (sometimes not even computed).}
    if not assigned R`PrincipalPolarizationsIsogenyClass then
        A:=Algebra(R);
        prec := 30;
        while true do
            try
                PHI:=pAdicPosCMType(A : precpAdic:=prec, precCC:=prec);
                break;
            catch e // precision error can happen
                prec *:= 2;
            end try;
        end while;
        oo:=OverOrders(R);
        output:=[];
        for iS in [1..#oo] do
            S:=oo[iS];
            test_S:=IsConjugateStable(S) and not exists{ P : P in NonGorensteinPrimes(S) | IsConjugateStable(P) and CohenMacaulayTypeAtPrime(S,P) eq 2 };
            // if test eq false then there is no PPAV with End = S.
            if test_S then
                // if S is Gorenstein the next part can be improved!
                icmS:=ICM_bar(S);
                for I in icmS do
                    pp:=PrincipalPolarizations(I,PHI);
                    if #pp gt 0 then
                        Append(~output,< I , pp >);
                    end if;
                end for;
            end if;
        end for;
        R`PrincipalPolarizationsIsogenyClass:=output;
    end if;
    return R`PrincipalPolarizationsIsogenyClass;
end intrinsic;

intrinsic PrintPrincipalPolarizationsIsogenyClass(R::AlgEtQOrd)->MonStgElt
{Given the order R=Z[F,V] of an ordinary squarefree isogeny class, it computes the principal polarizatons and return a string that can printed to file. This string can be loaded back in magma using LoadPrincipalPolarizationsIsogenyClass. The output is not distinguished.}
    A:=Algebra(R);
    nf:=Components(A);
    nf_poly:=[ Coefficients((DefiningPolynomial(K))) : K in nf ];

    str:="<\n";
    str cat:=RemoveBlanks(Sprint(nf_poly)) cat ",\n";
    _,zbR:=PrintSeqAlgEtQElt(ZBasis(R));
    str cat:=zbR cat ",\n";
    str cat:="<\n";
    ppav:=PrincipalPolarizationsIsogenyClass(R);
    for i->pair in ppav do
        I:=pair[1];
        ppols:=pair[2];
        _,strI:=PrintSeqAlgEtQElt(ZBasis(I));
        _,str_ppols:=PrintSeqAlgEtQElt(ppols);
        str cat:="<\n" cat strI cat "," cat str_ppols cat "\n>";
        if i ne #ppav then
            str cat:=",\n";
        else
            str cat:="\n";
        end if;
    end for;
    str cat:= ">\n>";
    return str;
end intrinsic;

// the next intrinsic was merged in DistinguishedRepresentativePolarizationGeneral which was then renamed DistinguishedRepresentativePolarization
intrinsic DistinguishedRepresentativePolarizationConjugateStableOrder(I::AlgEtQIdl,x0::AlgEtQElt) -> AlgEtQElt,RngIntElt,SeqEnum[RngIntElt]
{Given an ideal I such that (I:I) is conjugate stable, and an element x0 representing a polarization for I, we want to look at the set x0*u*\bar(u) where u runs over the units of (I:I)=S. We compute the image of this set via the Log map. We use ShortestVectors on this lattice, pullback the output in the algebra, computhe the action of the torsion units of S on these elements, represent them with respect to [V^(g-1),...,V,1,F,...,F^g], sort them with respec to the lexigographic order of their coefficients and take the smallest.
The output consists of pol,den,nums where
- pol is the distinguished representative of an isomorphism class of a polarization x0 of I;
- den and nums are sequence of integers representing the lcm of the denominators of and the numerators of the coefficients of pol wrt the ZFVBasis.}

    S:=MultiplicatorRing(I);
    require IsConjugateStable(S) : "implemented only for conjugate stable orders, at the moment";
    A:=Algebra(x0);
    g:=Dimension(A) div 2;
    F:=PrimitiveElement(A);
    basis:=ZFVBasis(A);

    if g eq #Components(A) then // then sub below would be the trivial group and the code would not modify x0. Early exit
        y0 := AbsoluteCoordinates([x0],basis);
        den := LCM([Denominator(c) : c in y0[1]]);
        nums := [den * c : c in y0[1]];
        return x0, den, nums;
    end if;

    homs:=HomsToC(A);
    prec:=Precision(Codomain(homs[1]));
    // are the homs sorted in conjugate pairs?
    assert forall{ k : k in [1..g] | Abs(homs[2*k-1](F) - ComplexConjugate(homs[2*k](F))) lt 10^-(prec div 2)};

    homs:=[homs[2*k-1] : k in [1..g]]; //one per conjugate pair to define the Log map
    US,uS:=UnitGroup(S);
    gens_US:=[ uS(g) : g in Generators(US) ]; // the torsion unit probably does do nothing

    sub:=sub< US | [(g*ComplexConjugate(g))@@uS : g in gens_US ] >;     // sub = < u * \bar u : u in S^* >
    gens_sub_inS:=[ uS(g) : g in Generators(sub) ];
    rnk_sub:=#gens_sub_inS;
    assert rnk_sub eq g-#Components(A);
    img_gens_sub:=Matrix([[ Log(Abs(h(g))) : h in homs ] : g in gens_sub_inS ]); // apply Log map
    L:=LatticeWithBasis(img_gens_sub); // before it was Lattice. But we want img_gens_sub to be the basis!
    img_x0:=Vector([ Log(Abs(h(x0))) : h in homs ]);
    closest_vects:=ClosestVectors(L,-img_x0); //note the minus sign!
    all_coords:=[ Coordinates(cv) : cv in closest_vects];
    candidates:=[ x0*&*[ gens_sub_inS[i]^coord[i] : i in [1..rnk_sub] ] : coord in all_coords ];
    // A priori, I believe that I should act on candidates with the torsion units of the totally real totally positive units in S
    // But there is only 1 (which also the torsion subgroup of sub = < u*\bar u>

    // Now, I sort the candidats with respect to lexicographic order of the coefficients wrt to [V^(g-1),...,V,1,F,...,F^g],
    // and take the smallest.
    sort_keys_candidates:=[ AbsoluteCoordinates([c],basis)[1] : c in candidates ];
    ParallelSort(~sort_keys_candidates,~candidates);
    den := LCM([Denominator(c) : c in sort_keys_candidates[1]]);
    nums := [den*c : c in sort_keys_candidates[1]];

    return candidates[1], den, nums;
end intrinsic;

intrinsic LoadPrincipalPolarizationsIsogenyClass(str::MonStgElt)->AlgEtQOrd
{Given a string produced with PrintPrincipalPolarizationsIsogenyClass, it returns the orders Z[F,V] after populating the attribute PrincipalPolarizationIsogenyClass, which contains the output of PrincipalPolarizationIsogneyClass. The string doesn't need to describe distinguished representatives.}
    data:=eval(str);
    PP:=PolynomialRing(Rationals());
    ff:=[ PP!f : f in data[1]];
    A:=EtaleAlgebra([NumberField(f) : f in ff ]);
    zbR:=[A!s : s in data[2]];
    R:=Order(zbR);
    pairs:=data[3];
    ppav:=[];
    for pair in pairs do
        I:=Ideal(R,[A!s : s in pair[1]]);
        I_pols:=[A!s : s in pair[2]];
        Append(~ppav,<I,I_pols>);
    end for;
    R`PrincipalPolarizationsIsogenyClass:=ppav;
    return R;
end intrinsic;

intrinsic PeriodMatrix(I::AlgEtQIdl,x0::AlgEtQElt,phi::AlgEtQCMType) -> AlgMatElt,AlgMatElt
{ Given an abelian variety I over a finite field and a principal polarization x0 computed wrt the CM-type phi, it returns the corresponding big and small period matrices. The precision of the approximation is determined by the precision of the cm-type.}
	A:=Algebra(I);
	zb:=ZBasis(I);
	N:=#zb;
    n:=N div 2;
    E := Matrix(Integers(),N,N,[Trace(ComplexConjugate(a*x0)*b) : a in zb, b in zb]); // added sign
    C, B := FrobeniusFormAlternating(E);
    // Check documentation of FrobeniusFormAlternating
    newb:= [ SumOfProducts(Eltseq(r),zb) : r in Rows(B) ];
    is_symplectic:=function(basis)
        n := #basis div 2;
        bil:=func<x,y | Trace(ComplexConjugate(y*x0)*x)>;
        G:=basis[1..n];
        B:=basis[n+1..2*n];
        return forall{i : i,j in [1..n] | bil(G[i],G[j]) eq 0 and bil(B[i],B[j]) eq 0 and bil(G[i],B[j]) eq KroneckerDelta(i,j)};
    end function;
    assert is_symplectic(newb);
    prec_factor:=0;
    while true do
        try
            homs:=Homs(phi);
            prec:=Precision(phi);
            bigPM := Matrix(Codomain(homs[1]),n,N,&cat[[F(b) : b in newb] : F in homs]);
            smallPM := Submatrix(bigPM,1,n+1,n,n)^-1*Submatrix(bigPM,1,1,n,n);
            test_symm:=forall{<i,j> : i,j in [1..n] | Abs(smallPM[i,j]-smallPM[j,i]) lt 10^(-(prec div 2)) };
            im_smallPM:=Matrix([[Im(x) : x in Eltseq(r)] :r in Rows(smallPM)]);
            test_pos_def:=forall{e : e in Eigenvalues(im_smallPM) | e[1] gt 0 };
            require test_symm and test_pos_def : "Precision issue. Increase the precision of the given cm-type";
            return bigPM,smallPM;
        catch e
            "We double the precision of the CMType";
            old_prec:=Precision(phi);
            prec_factor +:=1;
            phi:=ChangePrecision(phi,2^prec_factor*old_prec);
            assert Precision(phi) gt old_prec;
            go:=false;
        end try;
    end while;
end intrinsic;


intrinsic AllMinimalIsogenies(ZFV::AlgEtQOrd, N::RngIntElt : degrees:=0)->Assoc
{Given the ZFV order of a squarefree isogeny class, it returns an associative array, indexed by the distinguished representatives J of isomorphism classes, in which each entry contains an associative array with data describing isogenies to J. This data consists of a tuple ... 
//TODO finish descr
}
    isom_cl, icm_lookup := ICM_DistinguishedRepresentatives(ZFV);
    min_isog:=AssociativeArray();
    for I in isom_cl do
        min_isog[myHash(I)] := AssociativeArray();
        for J in isom_cl do
            min_isog[myHash(I)][myHash(J)] := [];
        end for;
    end for;
    for J in isom_cl do
        // J is over ZFV
        Ls := MaximalIntermediateIdeals(J,N*J);
        for L in Ls do
            deg := Index(J, L);
            if degrees cmpne 0 and not (deg in degrees) then
                continue;
            end if;
            I, x := ICM_Identify(L, icm_lookup);
            assert2 Index(J,x*I) eq deg;
            Append(~min_isog[myHash(I)][myHash(J)], <deg, x, L>); // x is a minimal isogeny from I to J of degree deg=#(J/L)
        end for;
    end for;
    return min_isog;
end intrinsic;

intrinsic IsogeniesByDegree(ZFV::AlgEtQOrd, degree_bounds::SeqEnum : important_pairs:=0) -> Assoc
{Given the ZFV order of a squarefree isogeny class, together with a sequence of integers, return an associative array A so that A[I][J][d] consists of all isogenies of degree d from I to J for all integers d dividing any element of degree_bounds.  Each isogeny is stored as a pair <x,L> where x is an element mapping I into J and L = x*I (which is a submodule of J of an appropriate index).}
    // imporant pairs, if given, should be a list of tuples <I,J> of distinguished representatives (see note below for how they're used)
    N := LCM(degree_bounds);
    degrees := {};
    proper_degrees := {};
    for B in degree_bounds do
        for d in Divisors(B) do
            if d eq 1 then continue; end if;
            Include(~degrees, d);
            // When looking for isogenies from I to Iv, we only care about isogenies between other ideals in that they help build these.  Since we'll always be composing with an extra minimal isogeny, we can drop the degree bounds for isogenies from I to J when J ne Iv (see keep_degree function below)
            if d eq B then continue; end if;
            Include(~proper_degrees, d);
        end for;
    end for;
    function keep_degree(I,J,d)
        if important_pairs cmpeq 0 or <I,J> in important_pairs then
            return d in degrees;
        else
            return d in proper_degrees;
        end if;
    end function;
    t0:=Cputime();
    min_isog := AllMinimalIsogenies(ZFV, N : degrees:=degrees);
    vprintf AllIsogenies : "time spent on AllMinimalIsogenies %o\n",Cputime(t0);
    isog := AssociativeArray();
    isom_cl:=ICM_DistinguishedRepresentatives(ZFV);
    for I in isom_cl do
        isog[myHash(I)] := AssociativeArray();
        for J in isom_cl do
            isog[myHash(I)][myHash(J)] := AssociativeArray();
            for dxL in min_isog[myHash(I)][myHash(J)] do
                d, x, L := Explode(dxL);
                if keep_degree(I, J, d) then
                    if not IsDefined(isog[myHash(I)][myHash(J)], d) then
                        isog[myHash(I)][myHash(J)][d] := [];
                    end if;
                    assert2 Index(J,L) eq d;
                    assert2 x*I eq L;
                    Append(~isog[myHash(I)][myHash(J)][d], <x, L>);
                end if;
            end for;
        end for;
    end for;
    while true do
        added_something := false;
        for J in isom_cl do
            for I in isom_cl do
                for K in isom_cl do
                    for m -> known in isog[myHash(I)][myHash(K)] do
                        for yL0 in known do
                            y, L0 := Explode(yL0);
                            for dxL in min_isog[myHash(K)][myHash(J)] do
                                d, x := Explode(dxL);
                                dm := d*m;
                                if keep_degree(I, J, dm) then
                                    L := x * L0;
                                    if not IsDefined(isog[myHash(I)][myHash(J)], dm) then
                                        isog[myHash(I)][myHash(J)][dm] := [<x*y, L>];
                                        added_something := true;
                                    else
                                        hsh := myHash(L);
                                        hashes := {myHash(M[2]) : M in isog[myHash(I)][myHash(J)][dm]};
                                        if not hsh in hashes then
                                            // myHash is collision free
                                            Append(~isog[myHash(I)][myHash(J)][dm], <x*y, L>);
                                            assert2 Index(J,x*y*I) eq dm;
                                            added_something := true;
                                        end if;
                                    end if;
                                end if;
                            end for;
                        end for;
                    end for;
                end for;
            end for;
        end for;
        if not added_something then
            break;
        end if;
    end while;
    return isog;
end intrinsic;




intrinsic OldNonprincipalPolarizations(ZFV::AlgEtQOrd, PHI::AlgEtQCMType, degree_bounds::SeqEnum[RngIntElt])->Assoc
{
Given the Z[F,V] order of an ordinary isogeny squarefree class, a p-Adic positive CMType PHI it returns an associative array whose keys are the distinguished representatives of all isomorphism classes. The value of the array for the isomorphism class I is the tuple <pol,den,nums,dec,label> where:
- pol is the distinguished representative of an isomorphism class of a polarizations of I;
- den and nums are sequence of integers representing the lcm of the denominators of and the numerators of the coefficients of pol wrt the ZFVBasis;
- dec is the output of DecompositionKernelOfIsogeny;
- label is the label of the polarized abelian variety, in the format g.q.coeffs-N.i.w.j-d.k.
}
    require not 1 in degree_bounds : "Do not use OldNonprincipalPolarizations to compute principal polarizations";
    isog_label:=IsogenyLabel(DefiningPolynomial(Algebra(ZFV)));
    t_tot:=Cputime();
    isom_cl, icm_lookup := ICM_DistinguishedRepresentatives(ZFV);
    can_reps_of_duals:=AssociativeArray();
    all_pols:=AssociativeArray(); // the output
    for J in isom_cl do
        Jv:=TraceDualIdeal(ComplexConjugate(J));
        // I am looking for pol such that pol*J c Jv
        JJ,JJ_to_Jv:=ICM_Identify(Jv,icm_lookup);
        can_reps_of_duals[J]:=<JJ,JJ_to_Jv,Jv>;
    end for;
    t0:=Cputime();
    all_isog:=IsogeniesByDegree(ZFV,degree_bounds : important_pairs:=[ < J , can_reps_of_duals[J][1] > : J in isom_cl ]);
    vprintf AllPolarizations : "time spent on IsogeniesByDegree: %o\n",Cputime(t0);
    t_can:=0;
    for J in isom_cl do
        assert assigned J`IsomLabel;
        isom_label:=J`IsomLabel;
        Jpols:=AssociativeArray(); // will contain all pols find, indexed by degree.
        S:=MultiplicatorRing(J);
        JJ,JJ_to_Jv,Jv:=Explode(can_reps_of_duals[J]);
        for d ->isog_J_JJ_d in all_isog[myHash(J)][myHash(JJ)] do
            if not IsSquare(d) then continue; end if; // the degree of a polarization has to be a square
            pols_deg_d:=[];
            for f in isog_J_JJ_d do
                isog:=f[1]*JJ_to_Jv;
                assert2 Index(JJ,f[1]*J) eq d;
                assert2 Index(Jv,isog*J) eq d;
                got_one:=false;
                for v in transversal_US_USplus(S) do
                    pp:=isog*v;
                    if is_polarization(pp,PHI) then
                        got_one:=true;
                        break v;
                    end if;
                end for;
                if got_one then
                    pols_deg_d cat:= [ pp*t : t in transversal_USplus_USUSb_general(S) ]; // this might contains isomorphic copies
                end if;
            end for;
            t_can_Jd:=Cputime();
            pols_deg_d_up_to_iso:={};
            for x0 in pols_deg_d do
                pol,den,nums:=DistinguishedRepresentativePolarization(J,x0);
                Include(~pols_deg_d_up_to_iso, <pol,den,nums>); //isomorphic pols will have the same distinguished rep
            end for;
            t_can +:=Cputime(t_can_Jd);
            assert2 forall{ pol : pol in pols_deg_d_up_to_iso | d eq Index(Jv,pol[1]*J) }; // sanity check
            if #pols_deg_d_up_to_iso gt 0 then
                // now, pols_deg_d_up_to_iso contains tuples <can,den,nums> each one 
                // representing an isomorphism class of polarizations of J of degree d.
                // we sort them to create the labels
                pols_deg_d_up_to_iso:=Setseq(pols_deg_d_up_to_iso);
                sort_keys:=[ [pol[2]] cat pol[3] : pol in pols_deg_d_up_to_iso ];
                ParallelSort(~sort_keys,~pols_deg_d_up_to_iso);
                pols_deg_d_up_to_iso_with_labels:=[];
                for k->pol in pols_deg_d_up_to_iso do
                    label:=Sprintf("%o-%o.%o",isom_label,d,k);
                    Append(~pols_deg_d_up_to_iso_with_labels,<pol[1],pol[2],pol[3],label>);
                end for;
                Jpols[d]:=[ < pol[1] , pol[2] , pol[3], DecompositionKernelOfIsogeny(J,Jv,pol[1]),pol[4] > : pol in pols_deg_d_up_to_iso_with_labels ];
            end if;
        end for;
        all_pols[J]:=Jpols;
    end for;
    vprintf AllPolarizations : "time spent on computing distinguished reps and removing duplicates: %o\n",t_can;
    vprintf AllPolarizations : "time spent on computing all polarizations: %o\n",Cputime(t_tot);
    return all_pols;
end intrinsic;
