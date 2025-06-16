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

intrinsic PPolPossIteration(S::AlgEtQOrd) -> SeqEnum
{Called internally from PPolIteration
//TODO what does it do?
}
    vprint User1: "Looking up canonical Pic basis";
    basis := CanonicalPicBasis(S);
    if IsGorenstein(S) and IsConjugateStable(S) and #PicardGroup(S) gt 1 then
        basisbar := BasisBar(S);
        tdp := TraceDualPic(S);
        function bar(x)
            coeffs := Eltseq(x);
            assert #coeffs eq #basisbar;
            if #coeffs eq 0 then return PicardGroup(S).0; end if;
            return &+[coeffs[i] * basisbar[i] : i in [1..#coeffs]];
        end function;
        function filter(x)
            return x + bar(x) eq tdp;
        end function;
        vprint User1: "Iterating with trick";
        return PicIteration(S, basis : filter:=filter);
    else
        vprint User1: "Iterating without trick";
        return PicIteration(S, basis);
    end if;
end intrinsic;

intrinsic PPolIteration(ZFV::AlgEtQOrd) -> List
{Given the Frobenius order, returns a list of quadruples <we, pic_ctr, I, den, nums, can>, where I is an ideal in the weak equivalence class we with picard group counter pic_ctr, and den (resp. nums) is the denominator (resp. numerators) of the coefficients of the distinguished representative can of the polarization (wrt the ZFVBasis).}
    A := Algebra(ZFV);
    vprint User1: "Computing CM type..."; t0 := Cputime();
    prec := 30;
    while true do
        try
            PHI:=pAdicPosCMType(A);
            break;
        catch e // precision error can happen
            prec *:= 2;
        end try;
    end while;
    vprint User1: Sprintf("Done with CM type in %o; computing canonical bases...", Cputime(t0)); t0 := Cputime();
    bases := CanonicalPicBases(ZFV); // sets CanonicalPicBasis for overorders
    vprint User1: Sprintf("Done computing canonical Pic bases in %o; starting through over orders", Cputime(t0)); t0 := Cputime();
    ans := [* *];
    for Sctr->S in OverOrders(ZFV) do
        know_no_PP := not IsConjugateStable(S) or exists{ P : P in NonGorensteinPrimes(S) | IsConjugateStable(P) and CohenMacaulayTypeAtPrime(S,P) eq 2 };
        if know_no_PP then
            vprint User1: "Skipping over order #", Sctr;
            continue;
        end if; // if true, there can't be any PPAV with this endomorphism ring
        vprint User1: "Computing WKICM_bar for over order #", Sctr;
        wkimS := WKICM_bar(S);
        vprint User1: Sprintf("Done computing WKICM_bar at %o; computing possible picard iteration", Cputime(t0));
        ppol_poss := PPolPossIteration(S);
        vprint User1: Sprintf("Done computing picard iteration at %o; iterating", Cputime(t0));
        for WE in wkimS do
            we := WELabel(WE);
            for tup in ppol_poss do
                I, pic_ctr := Explode(tup);
                WEI := WE * I;
                vprint User1: Sprintf("Computing principal polarizations at %o", Cputime(t0));
                pp := PrincipalPolarizations(WEI, PHI);
                vprint User1: Sprintf("Done computing principal polarizations at %o; iterating", Cputime(t0));
                for pol in pp do
                    can, den, nums := CanonicalRepresentativePolarization(WEI, pol);
                    vprint User1: Sprintf("Done computing canonical representative at %o", Cputime(t0));
                    Append(~ans, <we, pic_ctr, I, den, nums, can>);
                end for;
            end for;
        end for;
    end for;
    return ans;
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

intrinsic AllPolarizations(ZFV::AlgEtQOrd, PHI::AlgEtQCMType, degree_bounds::SeqEnum[RngIntElt])->Assoc
{Given the Z[F,V] order of an isogeny squarefree class, a p-Adic positive CMType PHI it returns an associative array whose keys are the canonical representatives of all isomorphism classes.
//TODO
.}
    //TODO this intrisc misses principal polarizations. I guess this is a feature, which we forgot to document in the description of the intrinsic. Added the require belo
    require not 1 in degree_bounds : "Do not use AllPolarizations to compute principal polarizations";
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
