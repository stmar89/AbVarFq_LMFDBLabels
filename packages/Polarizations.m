/* vim: set syntax=magma :*/

declare verbose AllPolarizations,1;
declare verbose pols_closest_vect,1;

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
                    can, den, nums := DistinguishedRepresentativePolarization(WEI, pol);
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


    // The Log-Minkowski lattice L of <u*\bar{u}> is constructed in the 
    // function below (since we want to control the precision)
    // It will have rank:
    rnk_sub:=#gens_sub;
    assert rnk_sub eq g-#Components(A);

    function Candidates(prec)
    // This function returns a boolean and, if true, all the vectors in L that are closest to the (image of) y0.
    // The input is a precision parameter. The returned boolean is false when we detect that the precision needs
    // to be increased.
        homs:=HomsToC(A : Prec:=prec); 
        prec:=Precision(Codomain(homs[1]));
        // are the homs sorted in conjugate pairs?
        assert forall{ k : k in [1..g]|Abs(homs[2*k-1](F) - ComplexConjugate(homs[2*k](F))) lt 10^-(prec div 2)};
        homs:=[homs[2*k-1] : k in [1..g]]; //one per conjugate pair to define the Log map

        Log_map:=function(g) //Log_\Phi
            return [ Log(Abs(h(g))) : h in homs ];
        end function;

        eps := 10^(-prec*0.9);
        img_gens_sub:=Matrix([Log_map(g) : g in gens_sub ]); // apply Log map
        L:=LatticeWithBasis(img_gens_sub);
        // we find all vectors in L closest to -img_x0
        img_x0:=Vector(Log_map(x0));
        vprintf pols_closest_vect: "running ClosestVectors in %o to %o ...",L,-img_x0;
        candidates:=ClosestVectors(L,-img_x0); //note the minus sign!
        vprintf pols_closest_vect: "done";

        norm_y0:=Norm(Vector(candidates[1])+img_x0);
        if not forall{c:c in candidates|Abs(Norm(Vector(c)+img_x0) - norm_y0) lt eps} then
            vprintf AllPolarizations : "prec: %o, candidates not small\n";
            return false, _;
        end if;

        // The procedure above is not independent of the initial x0.
        // Indeed, if we started with an isomorphic principal polarization x1, then we could get a different
        // set of candidates y1, also with `minimal' norm norm_y0
        // Each y1 will be of the form y1=l+y0 for some l in L.
        // By the triangular inequality we have that Norm(l) <= 4*norm_y0.
        // We enumerate elements of L satisfying this ineq and expand the list of candidates accordingly.
        // 4.4 is just to give it 10% margin error
        ss:=[Vector(s[1]):s in ShortVectors(L,4.4*norm_y0)];
        ss cat:=[-s:s in ss]; //ShortVectors is only up to sign
        Append(~ss,Parent(Vector(candidates[1]))!0); // we want to have the originaly candidates as well,
                                                     // we achieve this by adding the zero vector to ss.

        // Some of the short vectors s in ss might give c+s such that |c+s+y0| > |y0|, that is,
        // s moves c in the wrong direction. We want to exclude those s's.
        abs_diff := [Abs(Norm(Vector(c) +  s + img_x0) - norm_y0) : c in candidates, s in ss];
        cs_ss:=[<c,s> : c in candidates, s in ss ];
        ParallelSort(~abs_diff,~cs_ss);
        // after having sorted the `moved vectors' of the form c+s with respect to how far from y0, 
        // from closest to furthest, we keep only the ones which not further than the treshold eps.
        ind:=Max([i:i in [1..#abs_diff] | abs_diff[i] lt eps]);
        if ind lt #abs_diff and abs_diff[ind+1]^2 lt eps then
            // here we check that the first exclided one is relatively (in terms of eps) from y0.
            // If this is not the case, then the function returns false and
            // we need to increase the precision.
            vprintf AllPolarizations : "prec: %o, the first excluded candidate is still quite close to y0. Increase the precision.\n";
            return false, _;
        end if;
        cs_ss:=cs_ss[1..ind];
        vprintf AllPolarizations : "ind: %o\n", ind;
        vprintf AllPolarizations : "abs_diff: %o\n", abs_diff;

        // we coerce all the vectors into L
        extra_candidates := [L!(Vector(v[1])+v[2]) : v in cs_ss];
        vprintf AllPolarizations : "number extra candidates found using short vectors: %o\n",#extra_candidates-#candidates;
        vprintf AllPolarizations : "%o\n", [RealField(5) | Abs(Norm(Vector(c)+img_x0) - norm_y0) : c in extra_candidates];
        candidates:=extra_candidates;
        vprintf AllPolarizations : "candidates: %o\n",candidates;
        return true, candidates;
    end function;

    prec := 30;
    for i in [1..10] do
        b, candidates := Candidates(prec);
        if b then break; end if;
        prec *:= 2;
    end for;

    // now we move back to K
    all_coords:=[ Coordinates(cv) : cv in candidates];
    candidates:=[ x0*&*[ gens_sub[i]^coord[i] : i in [1..rnk_sub] ] : coord in all_coords ]; 
    // Now, I sort the candidates with respect to lexicographic order of the coefficients 
    // wrt to [V^(g-1),...,V,1,F,...,F^g],
    // and take the smallest.
    coordinates:=[ AbsoluteCoordinates([c],basis)[1] : c in candidates ];
    sort_keys_candidates:=[];
    for cand_coord in coordinates do
        den := LCM([Denominator(c) : c in cand_coord]);
        nums := [den*c : c in cand_coord];
        Append(~sort_keys_candidates,[den] cat nums);
    end for;
    ParallelSort(~sort_keys_candidates,~candidates);
    
    out_candidate:=candidates[1];
    sort_key_out_candidate:=sort_keys_candidates[1];
    den:=sort_key_out_candidate[1];
    nums:=sort_key_out_candidate[2..#sort_key_out_candidate];
    return out_candidate,den,nums;
end intrinsic;

intrinsic AllNonprincipalPolarizations(ZFV::AlgEtQOrd, PHI::AlgEtQCMType, degree_bounds::SeqEnum[RngIntElt])->Assoc
{Given the Z[F,V] order of an ordinary isogeny squarefree class, a p-Adic positive CMType PHI it returns an associative array whose keys are the distinguished representatives of all polarized isomorphism classes.  The degree d>1 loops over divisors of elements of degree_bounds.
The value of the array for the isomorphism class I is the tuple <pol,den,nums,dec,label> where:
- pol is the distinguished representative of an isomorphism class of a polarizations of I;
- den and nums are sequence of integers representing the lcm of the denominators of and the numerators of the coefficients of pol wrt the ZFVBasis;
- dec is the output of DecompositionKernelOfIsogeny;
- label is the label of the polarized abelian variety, in the format g.q.coeffs-N.i.w.j-d.k.}
    require not 1 in degree_bounds : "Do not use AllNonprincipalPolarizations to compute principal polarizations";
    isog_label:=IsogenyLabel(DefiningPolynomial(Algebra(ZFV)));
    t_tot := Cputime();
    isom_cl, icm_lookup := ICM_DistinguishedRepresentatives(ZFV);
    can_reps_of_duals := AssociativeArray();
    all_pols := AssociativeArray(); // the output
    t0 := Cputime();
    isog := RepresentativeIsogenies(ZFV, degree_bounds);
    vprintf AllPolarizations : "time spent on RepresentativeIsogenies: %o\n", Cputime(t0);
    t_can := 0;
    for I in isom_cl do
        // I am looking for pol such that pol*I c Iv
        isom_label:=I`IsomLabel;
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
                // x is the element inducing the isogeny from WI*h to WJ with image L, H is the subgroup of Pic(ZFV) that we can translate our domain by
                // So x also maps WI*h*Jpic to WJ*Jpic = J, so we just need to see if I can be reached from WI*h*Jpic using the subgroup H
                if Ipic - Jpic - h in H then
                    // This isogeny has the right domain and codomain to be a polarization.
                    got_one := false;
                    for v in transversal_US_USplus(S) do
                        pp := x*v; // TODO: need to think about how to use IsPrincipal appropriately here.
                        if is_polarization(pp, PHI) then
                            assert Index(Iv,pp*I) eq d;
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
                pol,den,nums:=DistinguishedRepresentativePolarization(J,x0);
                Include(~pols_deg_d_up_to_iso, <pol,den,nums>); //isomorphic pols will have the same distinguished rep
            end for;
            t_can +:=Cputime(t_can_Jd);
            assert forall{ pol : pol in pols_deg_d_up_to_iso | d eq Index(Iv, pol[1]*I) }; // sanity check
            if #pols_deg_d_up_to_iso gt 0 then
                // TODO this part has been moved here in July 2025. Check that everything is in order.
                // now, pols_deg_d_up_to_iso contains tuples <can,den,nums> each one 
                // representing an isomorphism class of polarizations of J of degree d.
                // we sort them to create the labels
                sort_keys:=[ [pol[2]] cat pol[3] : pol in pols_deg_d_up_to_iso ];
                ParallelSort(~sort_keys,~pols_deg_d_up_to_iso);
                pols_deg_d_up_to_iso_with_labels:=[];
                for k->pol in pols_deg_d_up_to_iso do
                    label:=Sprintf("%o-%o.%o",isom_label,d,k);
                    Append(~pols_deg_d_up_to_iso_with_labels,<pol[1],pol[2],pol[3],label>);
                end for;
                Ipols[d]:=[ < pol[1] , pol[2] , pol[3], DecompositionKernelOfIsogeny(I,Iv,pol[1]),pol[4] > : pol in pols_deg_d_up_to_iso_with_labels ];
            end if;
        end for;
        all_pols[I]:=Ipols;
    end for;
    vprintf AllPolarizations : "time spent on computing distinguished reps and removing duplicates: %o\n",t_can;
    vprintf AllPolarizations : "time spent on computing all polarizations: %o\n",Cputime(t_tot);
    return all_pols;
end intrinsic;

