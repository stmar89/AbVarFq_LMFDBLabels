/* vim: set syntax=magma :*/

declare verbose AllPolarizations,1;

declare attributes AlgEtQOrd : PrincipalPolarizationsIsogenyClass,
                               transversal_US_USplus,
                               transversal_USplus_USUSb;

// Depends on CHIMP for:
// ComplexFieldExtra, atoi, atoii, getrecs

transversal_US_USplus:=function(S)
// Given an order S, it returns a transveral in S of the quotient S^*/S^*_+, where
// S^*_+ is the subgroups of S^* consisting of totally real totally positive units.
    if not assigned S`transversal_US_USplus then
        US,uS:=UnitGroup(S);
        USplus:=TotallyRealPositiveUnitGroup(S);
        S`transversal_US_USplus:=[ uS(t) : t in Transversal(US,USplus)];
    end if;
    return S`transversal_US_USplus;
end function;

transversal_USplus_USUSb:=function(S)
// Given an order S=\bar{S}, it returns a transveral in S of the quotient S^*_+/<u\bar(u) : u in S^*> where
// S^*_+ is the subgroups of S^* consisting of totally real totally positive units.
    if not assigned S`transversal_USplus_USUSb then
        assert IsConjugateStable(S);
        US,uS:=UnitGroup(S);
        USplus:=TotallyRealPositiveUnitGroup(S);
        USUSb:=sub< USplus | [ USplus!((g*ComplexConjugate(g))@@uS) : g in [uS(g) : g in Generators(US) ]]>;
        S`transversal_USplus_USUSb:=[ uS(t) : t in Transversal(USplus,USUSb)];
    end if;
    return S`transversal_USplus_USUSb;
end function;

transversal_USplus_USUSb_general:=function(S)
// Given an order S, it returns a transveral in S of the quotient S^*_+/<u\bar(u) : u in S^*> where
// S^*_+ is the subgroups of S^* consisting of totally real totally positive units.
// It is very similar to transversal_USplus_USUSb, but works also when S is no conjugate stable.
    if not assigned S`transversal_USplus_USUSb then
        test,Sb:=IsConjugateStable(S);
        if test then
            _:=transversal_USplus_USUSb(S); // this caches the attribute
        else
            SSb:=S*Sb; // the smallest order containing both S and Sb
            U,u:=UnitGroup(SSb);
            US,uS:=UnitGroup(S);
            gens_US:=[ uS(g) : g in Generators(US) ];
            USUSb:=sub< U | [(g*ComplexConjugate(g))@@u : g in gens_US ] >;     // sub = < u * \bar u : u in S^* >
            USplus:=TotallyRealPositiveUnitGroup(S);
            USplus_USUSb:=sub<U | [ (uS(g))@@u : g in Generators(USplus) ] cat Setseq(Generators(USUSb)) >;
            USUSb:=sub< USplus_USUSb | [ USplus_USUSb!g : g in Generators(USUSb) ]>;
            S`transversal_USplus_USUSb:=[ u(t) : t in Transversal(USplus_USUSb,USUSb)];
        end if;
    end if;
    return S`transversal_USplus_USUSb;
end function;

is_polarization:=function(l,PHI)
// l an element of K, PHI a CMType, it returns wheather l is totally imaginary and PHI-positive, that is,
// Im(phi(l))>0 for every phi in PHI.
    test1:=l eq -ComplexConjugate(l);
    test2:=forall{phi : phi in Homs(PHI) | Im(phi(l)) gt 0 };
    return test1 and test2;
end function;

intrinsic PrincipalPolarizations(I::AlgEtQIdl,PHI::AlgEtQCMType)->SeqEnum[AlgEtQElt]
{Given an ideal I and a CM-Type PHI, returns all the principal polarizations of I with respect to PHI.}

    // First we test if there exists iso such that iso*I = Iv. If not, then I is not self-dual.
    // Assume that there exists such an iso.
    // Given iso1 with iso1*I=Iv, then iso1 is of the form iso1=v*iso, where v is in S^*.
    // Given two principal polarizations l and l1, then there eixsts a totally real totally positive unit v of S such that l1=v*l.
    // Moreover, (I,l) is isomorphic to (I,l1) as PPAV if and only if l1=u*\bar{u} for some u in S^*.
    // Combining these facts, we get that to determine whether there is a principal polarization of I, it suffices to check
    // elements of the form iso*v where v loops over a transversal of S^*/S^*_+,
    // where S^*_+ is the subgroupsof S^* consisting of totally real totally positive units.
    // If we find a principal polarization, say l, then all non-isomorphic one will be of the form l1=v*l, where v loops over a
    // transversal of S^*_+/<u*\bar{u} : u in S^*>.

    Iv:=TraceDualIdeal(ComplexConjugate(I));
    test,iso:=IsIsomorphic(Iv,I); // iso*I eq Iv
    if not test then
        Ipols:=[PowerStructure(AlgEtQElt)|]; //empty sseq
    else
        S:=MultiplicatorRing(I);
        got_one:=false;
        for u in transversal_US_USplus(S) do
            x:=u*iso;
            if is_polarization(x,PHI) then
                got_one:=true;
                break;
            end if;
        end for;
        if got_one then
            Ipols:=[ x*t : t in transversal_USplus_USUSb(S) ];
        else
            Ipols:=[PowerStructure(AlgEtQElt)|]; //empty sseq
        end if;
    end if;
    return Ipols;
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
{Given the order R=Z[F,V] of an ordinary squarefree isogeny class, it computes the principal polarizatons and return a string that can printed to file. This string can be loaded back in magma using LoadPrincipalPolarizationsIsogenyClass. The output is not canonical.}
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

intrinsic LoadPrincipalPolarizationsIsogenyClass(str::MonStgElt)->AlgEtQOrd
{Given a string produced with PrintPrincipalPolarizationsIsogenyClass, it returns the orders Z[F,V] after populating the attribute PrincipalPolarizationIsogenyClass, which contains the output of PrincipalPolarizationIsogneyClass. The string doesn't need to describe canonical representatives.}
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

intrinsic CanonicalRepresentativePolarization(I::AlgEtQIdl,x0::AlgEtQElt) -> AlgEtQElt,SeqEnum[FldRatElt]
{Given an ideal I and an element x0 representing a polarization for I, we want to look at the set x0*u*\bar(u) where u runs over the units of (I:I)=S. We compute the image of this set via the Log map. We use ShortestVectors on this lattice, pullback the output in the algebra, computhe the action of the torsion units of S on these elements, represent them with respect to [V^(g-1),...,V,1,F,...,F^g], sort them with respec to the lexigographic order of their coefficients and take the smallest.}

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
    L:=Lattice(img_gens_sub);
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



intrinsic LoadPPAVs(label, directory : prec := 100) -> SeqEnum
{ loads precomputed PPAVs in an isogeny class }
    recs := getrecs(directory cat "/av_fq_pol_output/" cat label);
    g, q, f := LabelToPoly(label);

    R := LoadSchemaWKClasses(Read(directory cat "/wk_classes/" cat label cat "_schema.txt"));
    reps_isom, _ := ICM_CanonicalRepresentatives(R);
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

intrinsic PeriodMatricesCanonicalLift(label, directory, prec) -> SeqEnum, SeqEnum
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

intrinsic NonprincipalPolarizations(ZFV::AlgEtQOrd, PHI::AlgEtQCMType, degree_bounds::SeqEnum[RngIntElt])->Assoc
{Given the Z[F,V] order of an isogeny squarefree class, a p-Adic positive CMType PHI it returns an associative array whose keys are the canonical representatives of all isomorphism classes.
//TODO
.}
    t_tot := Cputime();
    isom_cl, icm_lookup := ICM_CanonicalRepresentatives(ZFV);
    can_reps_of_duals := AssociativeArray();
    all_pols := AssociativeArray(); // the output
    t0 := Cputime();
    isog := RepresentativeIsogenies(ZFV, degree_bounds);
    vprintf AllPolarizations : "time spent on IsogeniesByDegree: %o\n", Cputime(t0);
    t_can := 0;
    for I in isom_cl do
        // I am looking for pol such that pol*I c Iv
        S := MultiplicatorRing(I);
        Iv := TraceDualIdeal(ComplexConjugate(I));
        J, J_to_Iv := ICM_Identify(Iv, icm_lookup);
        WI := I`WErep; Ipic := I`Pelt;
        WJ := J`WErep; Jpic := J`Pelt;
        Ipols:=AssociativeArray();
        for d -> isog_I_J_d in isog[myHash(WI)][myHash(WJ)] do
            pols_deg_d := [];
            for data in isog_I_J_d do
                x, h, H, L := Explode(data);
                // x is the element inducing the isogeny from WI+h to WJ with image L, H is the subgroup of Pic(ZFV) that we can translate our domain by
                // So x also maps WI+h+Jpic to WJ+Jpic = J, so we just need to see if I can be reached from WI+h+Jpic using the subgroup H
                if Ipic - Jpic - h in H then
                    // This isogeny has the right domain and codomain to be a polarization.
                    got_one := false;
                    for v in transversal_US_USplus(S) do
                        pp := x*v; // TODO: need to think about how to use IsPrincipal appropriately here.
                        if is_polarization(pp, PHI) then
                            got_one := true;
                            break;
                        end if;
                    end for;
                    if got_one then
                        pols_deg_d cat:= [ pp*t : t in transversal_USplus_USUSb_general(S) ]; // this might contain isomorphic copies
                    end if;
                end if;
            end for;
            t_can_Jd:=Cputime();
            pols_deg_d_up_to_iso:={};
            for x0 in pols_deg_d do
                pol,seq:=CanonicalRepresentativePolarizationGeneral(J,x0);
                Include(~pols_deg_d_up_to_iso, <pol,seq>); //isomorphic pols will have the same canonical rep
            end for;
            t_can +:=Cputime(t_can_Jd);
            assert2 forall{ pol : pol in pols_deg_d_up_to_iso | d eq Index(Iv, pol[1]*I) }; // sanity check
            if #pols_deg_d_up_to_iso gt 0 then
                Ipols[d]:=[ < pol[1] , pol[2] , DecompositionKernelOfIsogeny(I, Iv, pol[1]) > : pol in pols_deg_d_up_to_iso ];
            end if;
        end for;
        all_pols[I]:=Ipols;
    end for;
    vprintf AllPolarizations : "time spent on computing canonical reps and removing duplicates: %o\n",t_can;
    vprintf AllPolarizations : "time spent on computing all polarizations: %o\n",Cputime(t_tot);
    return all_pols;
end intrinsic;

intrinsic AllPolarizations(ZFV::AlgEtQOrd, PHI::AlgEtQCMType, degree_bounds::SeqEnum[RngIntElt])->Assoc
{Given the Z[F,V] order of an isogeny squarefree class, a p-Adic positive CMType PHI it returns an associative array whose keys are the canonical representatives of all isomorphism classes.
//TODO
.}
    t_tot:=Cputime();
    isom_cl, icm_lookup := ICM_CanonicalRepresentatives(ZFV);
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
                pol,den,nums:=CanonicalRepresentativePolarizationGeneral(J,x0);
                Include(~pols_deg_d_up_to_iso, <pol,den,nums>); //isomorphic pols will have the same canonical rep
            end for;
            t_can +:=Cputime(t_can_Jd);
            assert2 forall{ pol : pol in pols_deg_d_up_to_iso | d eq Index(Jv,pol[1]*J) }; // sanity check
            if #pols_deg_d_up_to_iso gt 0 then
                Jpols[d]:=[ < pol[1] , pol[2] , pol[3], DecompositionKernelOfIsogeny(J,Jv,pol[1]) > : pol in pols_deg_d_up_to_iso ];
            end if;
        end for;
        all_pols[J]:=Jpols;
    end for;
    vprintf AllPolarizations : "time spent on computing canonical reps and removing duplicates: %o\n",t_can;
    vprintf AllPolarizations : "time spent on computing all polarizations: %o\n",Cputime(t_tot);
    return all_pols;
end intrinsic;

intrinsic CanonicalRepresentativePolarizationGeneral(I::AlgEtQIdl,x0::AlgEtQElt) -> AlgEtQElt,SeqEnum[FldRatElt]
{Given an ideal I and an element x0 representing a polarization for I, we want to look at the set x0*u*\bar(u) where u runs over the units of (I:I)=S. We compute the image of this set via the Log map. We use ShortestVectors on this lattice, pullback the output in the algebra, computhe the action of the torsion units of S on these elements, represent them with respect to [V^(g-1),...,V,1,F,...,F^g], sort them with respect to the lexigographic order of their coefficients and take the smallest.}
// this is very similar to the code of CanonicalRepresentativePolarization
    S:=MultiplicatorRing(I);
    test,Sb:=IsConjugateStable(S);
    if test then 
        return CanonicalRepresentativePolarization(I,x0);
    end if;

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

    // this bit is different from CanonicalRepresentativePolarization
    SSb:=S*Sb; // the smallest order containing both S and Sb
    U,u:=UnitGroup(SSb);
    US,uS:=UnitGroup(S);
    gens_US:=[ uS(g) : g in Generators(US) ];
    sub:=sub< U | [(g*ComplexConjugate(g))@@u : g in gens_US ] >;     // sub = < u * \bar u : u in S^* >
    gens_sub:=[ u(g) : g in Generators(sub) ];
    // end of differences, except gens_sub_inS has been renamed to gens_sub (since they are in SSb, not necessarily in S).


    rnk_sub:=#gens_sub;
    assert rnk_sub eq g-#Components(A);
    img_gens_sub:=Matrix([[ Log(Abs(h(g))) : h in homs ] : g in gens_sub ]); // apply Log map
    L:=Lattice(img_gens_sub);
    img_x0:=Vector([ Log(Abs(h(x0))) : h in homs ]);
    closest_vects:=ClosestVectors(L,-img_x0); //note the minus sign!
    all_coords:=[ Coordinates(cv) : cv in closest_vects];
    candidates:=[ x0*&*[ gens_sub[i]^coord[i] : i in [1..rnk_sub] ] : coord in all_coords ]; 
    // A priori, I believe that I should act on candidates with the torsion units of the totally real totally positive units in S
    // But there is only 1 (which also the torsion subgroup of sub = < u*\bar u>

    // Now, I sort the candidates with respect to lexicographic order of the coefficients wrt to [V^(g-1),...,V,1,F,...,F^g],
    // and take the smallest.
    sort_keys_candidates:=[ AbsoluteCoordinates([c],basis)[1] : c in candidates ];
    ParallelSort(~sort_keys_candidates,~candidates);
    den := LCM([Denominator(c) : c in sort_keys_candidates[1]]);
    nums := [den*c : c in sort_keys_candidates[1]];

    return candidates[1], den, nums;
end intrinsic;

/*
    fld_m_files:="~/packages_github/AbVarFq/LMFDB/";
    fld:="~/266_wk_icm_rec/";
    fld_schema_wk:=fld cat "labelling/parallel/output/";
    AttachSpec(fld cat "AlgEt/spec");
    load "~/999_LMFDB_isogeny_label_functions.txt";
    P<x>:=PolynomialRing(Integers());
    Attach(fld_m_files cat "padictocc.m");
    Attach(fld_m_files cat "polarizations.m");

    t0:=Cputime();
        //file:=fld_schema_wk cat "2.128.a_bf_schema.txt";
        //file:=fld_schema_wk cat "3.9.d_j_o_schema.txt";
        time R:=LoadSchemaWKClasses(Read(file));
        time str:=PrintPrincipalPolarizationsIsogenyClass(R);
        time S:=LoadPrincipalPolarizationsIsogenyClass(str);
        time ppavs:=PrincipalPolarizations(S);
        "We have", &+[ #p[2] : p in ppavs ], "ppavs";
        PHI:=CMType(ppavs[1,2]);
        for p in ppavs do
            pp:=p[2];
            PeriodMatrix(p[1],pp,PHI);
        end for;
    t1:=Cputime(t0);
    "Tot time",t1;
*/
