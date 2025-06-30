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

intrinsic PPolPossIteration(S::AlgEtQOrd) -> SeqEnum
{Called internally from PPolIteration
//TODO what does it do?
}
    vprint User1: "Looking up distinguished Pic basis";
    basis := DistinguishedPicBasis(S);
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
{Given the Frobenius order, returns a list of quadruples <we, pic_ctr, I, den, nums, can, label>, where:
- I is a fractional ZFV-ideal;
- we is the distinguished representative of the weak equivalence class of I;
- pic_ctr is the picard counter of I; //TODO ??? 
- can is the distinguished representative of an isomorphism class of a polarization x0 of I;
- den and nums are sequence of integers representing the lcm of the denominators of and the numerators of the coefficients of can wrt the ZFVBasis;
- label is the label of the principally polarized abelian variety, in the format g.q.coeffs-N.i.w.j-1.k.}
    A := Algebra(ZFV);
    isog_label:=IsogenyLabel(DefiningPolynomial(A));
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
    vprint User1: Sprintf("Done with CM type in %o; computing distinguished bases...", Cputime(t0)); t0 := Cputime();
    bases := DistinguishedPicBases(ZFV); // sets DistinguishedPicBasis for overorders
    vprint User1: Sprintf("Done computing distinguished Pic bases in %o; starting through over orders", Cputime(t0)); t0 := Cputime();
    ans := [* *];
    for Sctr->S in OverOrders(ZFV) do
        know_no_PP := not IsConjugateStable(S) or exists{ P : P in NonGorensteinPrimes(S) | IsConjugateStable(P) and CohenMacaulayTypeAtPrime(S,P) eq 2 };
        if know_no_PP then
            vprint User1: "Skipping over order #", Sctr;
            continue;
        end if; // if true, there can't be any PPAV with this endomorphism ring
        vprint User1: "Computing WKICM_bar for over order #", Sctr;
        // wkimS := WKICM_bar(S); 20250617: I have changed this line into the next one.
        wkimS := WKICM_barDistinguishedRepresentatives(S);
        vprint User1: Sprintf("Done computing WKICM_bar at %o; computing possible picard iteration", Cputime(t0));
        ppol_poss := PPolPossIteration(S);
        vprint User1: Sprintf("Done computing picard iteration at %o; iterating", Cputime(t0));
        for WE in wkimS do
            we := WELabel(WE); // format of we: g.q.coeffs-N.i.w
            for tup in ppol_poss do
                I, pic_ctr := Explode(tup); // I is the distinguised rep of the element of Pic(S) with counter pic_ctr=j
                WEI := WE * I; //this is a distinguished rep of the corresponding isomorphism class with label g.q.coeffs-N.i.w.j
                WEI`IsomLabel:=Sprintf("%o.%o",we,pic_ctr);
                vprint User1: Sprintf("Computing principal polarizations at %o", Cputime(t0));
                pp := PrincipalPolarizations(WEI, PHI);
                vprint User1: Sprintf("Done computing principal polarizations at %o; iterating", Cputime(t0));
                sort_keys_pp:=[];
                ans_pp:=[];
                for pol in pp do
                    can, den, nums := DistinguishedRepresentativePolarizationWEI, pol);
                    assert can*WEI eq TraceDualIdeal(ComplexConjugate(WEI));
                    Append(~sort_keys_pp,[den] cat nums);
                    vprint User1: Sprintf("Done computing distinguished representative at %o", Cputime(t0));
                    Append(~ans_pp, <we, pic_ctr, WEI, den, nums, can>);
                end for;
                //we sort the polarizations to construct the labels
                ParallelSort(~sort_keys_pp,~ans_pp);
                // we construct the labels and append exerything to the output ans
                for k->pol_data in ans_pp do
                    label_kth_pol:=Sprintf("%o-%o.%o",WEI`IsomLabel,1,k); // the degree is hard coded to 1
                    we, pic_ctr, WEI, den, nums, can := Explode(pol_data);
                    Append(~ans, <we, pic_ctr, WEI, den, nums, can,label_kth_pol>);
                end for;
            end for;
        end for;
    end for;
    return ans;
end intrinsic;

intrinsic AllNonprincipalPolarizations(ZFV::AlgEtQOrd, PHI::AlgEtQCMType, degree_bounds::SeqEnum[RngIntElt])->Assoc
{Given the Z[F,V] order of an ordinary isogeny squarefree class, a p-Adic positive CMType PHI it returns an associative array whose keys are the distinguished representatives of all isomorphism classes. The value of the array for the isomorphism class I is the tuple <pol,den,nums,dec,label> where:
- pol is the distinguished representative of an isomorphism class of a polarizations of I;
- den and nums are sequence of integers representing the lcm of the denominators of and the numerators of the coefficients of pol wrt the ZFVBasis;
- dec is the output of DecompositionKernelOfIsogeny;
- label is the label of the polarized abelian variety, in the format g.q.coeffs-N.i.w.j-d.k.}
    require not 1 in degree_bounds : "Do not use AllNonprincipalPolarizations to compute principal polarizations";
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
                // now, pols_deg_d_up_to_iso contains tuples <can,den,nums> each one representing an isomorphism class of polarizations of 
                // J of degree d.
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

intrinsic DistinguishedRepresentativePolarization(I::AlgEtQIdl,x0::AlgEtQElt) -> AlgEtQElt,RngIntElt,SeqEnum[RngIntElt]
{Given an ideal I and an element x0 representing a polarization for I, we want to look at the set x0*u*\bar(u) where u runs over the units of (I:I)=S. We compute the image of this set via the Log map. We use ShortestVectors on this lattice, pullback the output in the algebra, computhe the action of the torsion units of S on these elements, represent them with respect to [V^(g-1),...,V,1,F,...,F^g], sort them with respect to the lexigographic order of their coefficients and take the smallest.
The output consists of pol,den,nums where
- pol is the distinguished representative of an isomorphism class of a polarization x0 of I;
- den and nums are sequence of integers representing the lcm of the denominators of and the numerators of the coefficients of pol wrt the ZFVBasis.}

    S:=MultiplicatorRing(I);
    is_conjugate_stable,Sb:=IsConjugateStable(S);

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

    Log_map:=function(g)
        return [ Log(Abs(h(g))) : h in homs ];
    end function;
        
    
    if is_conjugate_stable then
        // this version is slightly faster
        US,uS:=UnitGroup(S);
        gens_US:=[ uS(g) : g in Generators(US) ]; // the torsion unit probably does do nothing

        sub:=sub< US | [(g*ComplexConjugate(g))@@uS : g in gens_US ] >;     // sub = < u * \bar u : u in S^* >
        gens_sub:=[ uS(g) : g in Generators(sub) ];
    else
        SSb:=S*Sb; // the smallest order containing both S and Sb
        U,u:=UnitGroup(SSb);
        US,uS:=UnitGroup(S);
        gens_US:=[ uS(g) : g in Generators(US) ];
        sub:=sub< U | [(g*ComplexConjugate(g))@@u : g in gens_US ] >;     // sub = < u * \bar u : u in S^* >
        gens_sub:=[ u(g) : g in Generators(sub) ];
    end if;

    // we construct the lattice
    rnk_sub:=#gens_sub;
    assert rnk_sub eq g-#Components(A);
    img_gens_sub:=Matrix([Log_map(g) : g in gens_sub ]); // apply Log map
    L:=LatticeWithBasis(img_gens_sub);
    // we find all vectors in L closest to -img_x0
    img_x0:=Vector(Log_map(x0));
    candidates:=ClosestVectors(L,-img_x0); //note the minus sign!

    norm_y0:=Norm(candidates[1]);
    prec:=30; // this precision parameter is set so because L is contructed using the default precision 30
    assert forall{c:c in candidates|Abs(Norm(c) - norm_y0) lt 10^-prec};
    // The procedure above is not independent of the initial x0.
    // Indeed, if we started with an isomorphic principal polarization x1, then we could get a different
    // set of candidates y1, also with `minimal' norm norm_y0
    // Each y1 will be of the form y1=l+y0 for some l in L.
    // By the triangular inequality we have that Norm(l) <= 2*norm_y0.
    // We enumerate elements of L satisfying this ineq and expand the list of candidates accordingly.
    ss:=[Vector(s[1]):s in ShortVectors(L,2*norm_y0)];
    ss cat:=[-s:s in ss]; //ShortVectors is only up to sign
    extra_candidates:=[];
    norm_y0_eps:=norm_y0+10^-prec;
    for s in ss,c in candidates do
        cs:=c+s;
        ncs:=Norm(cs);
        if ncs lt norm_y0_eps then
            assert Abs(ncs - norm_y0) lt 10^-prec; 
            Append(~extra_candidates,cs);
        end if;
    end for;
    vprintf AllPolarizations : "number extra candidates: %o\n",#extra_candidates;
    candidates cat:=extra_candidates;

    // now we move back to K
    all_coords:=[ Coordinates(cv) : cv in candidates];
    candidates:=[ x0*&*[ gens_sub[i]^coord[i] : i in [1..rnk_sub] ] : coord in all_coords ]; 
    // Now, I sort the candidates with respect to lexicographic order of the coefficients 
    // wrt to [V^(g-1),...,V,1,F,...,F^g],
    // and take the smallest.
    sort_keys_candidates:=[ AbsoluteCoordinates([c],basis)[1] : c in candidates ];
    ParallelSort(~sort_keys_candidates,~candidates);
    den := LCM([Denominator(c) : c in sort_keys_candidates[1]]);
    nums := [den*c : c in sort_keys_candidates[1]];

    return candidates[1], den, nums;
end intrinsic;

