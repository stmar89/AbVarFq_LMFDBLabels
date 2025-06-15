/* vim: set syntax=magma : */
/*
    We store here the intrinsics that have been superseeded.
*/

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

