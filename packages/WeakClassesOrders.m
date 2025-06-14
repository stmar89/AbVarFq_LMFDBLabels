/* vim: set syntax=magma : */
/*

*/
    
declare attributes AlgEtQ : ZFVBasis;
declare attributes AlgEtQIdl : WELabel; // stores the label N.i.j of the weak eq class see FillSchema
declare attributes AlgEtQOrd : WKICM_barCanonicalRepresentatives, // a sequence, indexed as WKICM_bar, containing the 
                                                                // canonical representative of each weak class
                               WELabel; // stores the label N.i.1 of the order as a weak eq class see FillSchema


intrinsic ZFVBasis(A::AlgEtQ) -> SeqEnum[AlgEtQElt]
{The basis V^(g-1),...,V,1,F,...,F^g}
    if assigned A`ZFVBasis then
        return A`ZFVBasis;
    end if;
    g,q:=DimensionSizeFiniteField(A);
    F:=PrimitiveElement(A);
    V:=q/F;
    basis:=[ V^i : i in [g-1..0 by -1]] cat [F^i : i in [1..g]];
    A`ZFVBasis := basis;
    return basis;
end intrinsic;

intrinsic WKICM_barCanonicalRepresentatives(S::AlgEtQOrd)->SeqEnum[AlgEtQIdl]
{Let S be an order in an étale algebra K=Q[F]=Q[x]/(h), where h is a squarefree q-Weil polynomial. This intrinsic returns a sequence of canonical representatives of the classes in WKICM_bar(S), in the same order.
The canonical represenatative is defined as follows:
- If S is Gorenstein then there is only one weak class with multiplcator ring S, which will be represented by OneIdeal(S).
- If S has Cohen Macaulay type 2, then 
    -- put dSt:=d*St, where St is the TraceDualIdeal(S) and d is the smallest integer such that dSt c S.
    -- let the P1,...,Pn denote the primes of S at which S is non-Gorenstein, that is, has Cohen Macaulay type exactly 2.
    -- let m1,...,mn be positive integers such that Pi^mi is contained in dSt locally tt Pi. These mi exists because S is Noetherian.
  Each ideal I with (I:I)=S satisfies either I_Pi \simeq S_Pi or I_Pi \simeq dSt_Pi. 
  Explicitely, J = \sum_i ( (I_i + P_i^mi )*\prod_(j ne i)j^mj ), where I_i = S if I_Pi\simeq S_Pi and I_i=dSt if I_Pi\simeq dSt_Pi.
  Note that if we replace mi with a bigger integer, the ideal J does not change.
  Also, note that J_Pi = (I_i)_Pi for each i, and J_P=S_P for every other primes P of S.
  For more details, see Theorem 6.2 and Lemma 6.4 in "arXiv:2206.03758".
- If S has Cohen Macaulay type > 2 then:
    -- let P1,...,Pn be the singular primes of S.
    -- put Ti=(Pi:Pi) for each i
    -- put Gi = (Ti^*/S^*) x ker( Pic(S)->Pic(T) | [L]:->[LT] ).
    -- let T be Ti such that Gi is smallest, if there is more than one with the same size, pick the i with Pi of smallest SortKey.
    -- let K be a set of representatives of the classes in the ker, such that LT=T.
    -- let U be a transversal of (T^*/S^*).
    -- By recursion, let J1,...,Js be the canonical representatives of WKICM_bar(T).
  Each class in WKICM_bar admits a representative I0 such that I0*T=Ji for a unique idex i.
  All ideals I, weakly equivalent to I0, satisfying I*T=J_i are of the form I=u*L*I0 for unique u in U and L in K.
  We list all of them and define the canonical representative of the weak equivalence class of I0 to be the one 
  with smallest output of my_hnf(I,basis), sorted lexicographically, where basis = [ V^(g-1),...,V , 1 , F, ... F^g).
  }

    if not assigned S`WKICM_barCanonicalRepresentatives then
        cm:=CohenMacaulayType(S);
        if cm eq 1 then
            S`WKICM_barCanonicalRepresentatives:=[OneIdeal(S)];
        else
            if cm eq 2 then
                pp:=NonGorensteinPrimes(S);
                St:=TraceDualIdeal(S);
                d:=Index(St,OneIdeal(S));
                dSt:=d*St; // dSt c S.
                if #pp eq 1 then
                    S`WKICM_barCanonicalRepresentatives:=[OneIdeal(S),dSt];
                else
                    pows:=[];
                    for P in pp do
                        _,p,e:=IsPrimePower(Integers()!Index(S,P)); // e=Valuation(p,Index(S,P));
                        m:=Valuation(Index(S,dSt),p) div e; // Here we are using Proposition 4.2 of Klueners and Pauli 
                                                          // "Computing residue class rings ...".
                                                          // With such an m we have:
                                                          //   pp[i]^m \subseteq I_pp[i]
                        Append(~pows,P^m);
                    end for;
                    pows_hat:=[ &*[ pows[j] : j in [1..#pp] | j ne i ] : i in [1..#pp] ];
                    Is:=[ seq : seq in CartesianProduct([[OneIdeal(S),dSt] : i in [1..#pp]]) ];
                    out:=[];
                    for I in Is do
                        L:=&+[ (I[i]+pows[i]) * pows_hat[i] : i in [1..#pows_hat]];
                        assert IsInvertible(L) select L eq OneIdeal(S) else L ne OneIdeal(S);
                        Append(~out,L);
                    end for;
                    S`WKICM_barCanonicalRepresentatives:=out;
                end if;
            else //general case
                pp:=SingularPrimes(S);
                PS,pS:=PicardGroup(S);
                US,uS:=UnitGroup(S);

                G_acting:=function(P)
                    T:=MultiplicatorRing(P);
                    PT,pT:=PicardGroup(T);
                    UT,uT:=UnitGroup(T);
                    US_sub:=sub<UT | [ uS(US.i)@@uT : i in [1..Ngens(US)]] >;
                    ext:=hom<PS->PT | s:->(T!!pS(s))@@pT>;
                    ker:=[ pS(L) : L in Kernel(ext)];
                    // we need to replace L in ker so that T!!L = T.
                    for i in [1..#ker] do
                        L:=ker[i];
                        test,x:=IsPrincipal(T!!L);
                        assert test;
                        ker[i]:=(1/x)*L;
                    end for;
                    // next one is time consuming
                    assert forall{L : L in ker | T!!L eq T};
                    units:=[ uT(u) : u in Transversal(UT,US_sub) ];
                    return <T,units,ker>;
                end function;

                A:=Algebra(S);
                f:=DefiningPolynomial(A);
                basis:=ZFVBasis(A);
                pp:=SortSingularPrimes(S);
                G:=G_acting(pp[1]);
                size:=#G[2]*#G[3];
                for i in [2..#pp] do
                    G_i:=G_acting(pp[i]);
                    size_i:=#G_i[2]*#G_i[3];
                    if (size_i lt size) then
                        // if size_i eq size then I keep what I already have, since the primes are sorted
                        G:=G_i;
                        size:=size_i;
                    end if;
                end for;
                T:=G[1];
                // T now contains the one with the smallest G_acting
                wkS:=WKICM_bar(S);
                wkT_can:=$$(T); // recursion here
                wkS_can:=[];
                for iI->I in wkS do
                    if IsInvertible(I) then
                        Append(~wkS_can,OneIdeal(S));
                    else
                        TI:=T!!I;
                        stop:=false;
                        j:=0;
                        repeat
                            j+:=1;
                            J:=wkT_can[j];
                            stop:=IsWeakEquivalent(TI,J);
                        until stop;
                        L:=ColonIdeal(J,TI);
                        x,xL:=MakeCoprime(L,T!!Conductor(S));
                        L1:=S!!xL meet OneIdeal(S); // L1 satisfies T!!L1=xL.
                        assert IsInvertible(L1);
                        I1:=(1/x)*I*L1; // I1 satisfies T!!I1 = J and I1 is weak eq to I.
                        assert IsWeakEquivalent(I1,I);
                        assert T!!I1 eq J;
                        candidates:=[ u*L*I1 : u in G[2] , L in G[3] ];
                        assert forall{ I2 : I2 in candidates | T!!I2 eq J }; //This is time consuming
                        sort_keys_candidates:=[ my_hnf(I1,basis) : I1 in candidates ];
                        ParallelSort(~sort_keys_candidates,~candidates);
                        Append(~wkS_can,candidates[1]);
                    end if;
                end for;
                S`WKICM_barCanonicalRepresentatives:=wkS_can;
            end if;
        end if;
    end if;
    return S`WKICM_barCanonicalRepresentatives;
end intrinsic;

intrinsic seq_of_dims(I::AlgEtQIdl) -> SeqEnum[RngIntElt]
{Given an ideal I over an order S, not necessarily the multipicator ring, it returns the sequence of integers dim_(S/P) (I/PI), where P runs over the singular primes of S, sorted according to the lexicographic order of their SortKeys.}
    S:=Order(I);
    if IsMaximal(S) then
        return [PowerStructure(RngIntElt)|];
    else
        return [ Ilog(Integers()!Index(S,P) , Integers() ! Index(I,P*I) ) : P in SortSingularPrimes(S) ];
    end if;
end intrinsic;

intrinsic SortKeysWKICM_bar(S::AlgEtQOrd) -> SeqEnum[SeqEnum[RngIntElt]]
{Given an order S, it returns the sequence of SortKeys of the classes in WKICM_bar(S). The SortKey is a sequence of integers consistsing of two parts, dims cat hnf_can, defined as follows:
- dims is the output of seq_of_dims(I) for any representative of the class.
- if S has Cohen Maulay type <=2, then hnf_can is left empty, otherwise is the output of my_hnf(I_can), 
  where I_can is the canonical representative of the class. See WKICM_barCanonicalRepresentatives for the 
  definition of canonical representative.
Note that from the SortKey, and the order S, one can always reconstruct the canonical representative of the class.
}
    cm:=CohenMacaulayType(S);
    if cm le 2 then
        return [ seq_of_dims(I) : I in WKICM_bar(S) ];
    else
        basis:=ZFVBasis(Algebra(S));
        return [ seq_of_dims(I) cat my_hnf(I,basis) : I in WKICM_barCanonicalRepresentatives(S) ];
    end if;
end intrinsic;

intrinsic SortKeysOrders(seq::SeqEnum[AlgEtQOrd]) -> SeqEnum[SeqEnum[RngIntElt]]
{Let S be an order in an étale algebra K=Q[F]=Q[x]/(h), where h is a squarefree q-Weil polynomial. 
The SortKey of S is consists of two integers N.i where:
- N=Index(O,S) with O the maximal order of the algebra.
- i is the index that determines, the position of S in the list of orders with the same N, sorted lexicographically 
  with respect to the output of my_hnf(S,basis) with basis = [ V^(g-1),...,V , 1 , F, ... F^g).}
    A:=Algebra(seq[1]);
    basis:=ZFVBasis(A);
    O:=MaximalOrder(A);
    return [ [Index(O,S)] cat my_hnf(S,basis) : S in seq ];
end intrinsic;


intrinsic two_generating_set(I::AlgEtQIdl,basis::SeqEnum[AlgEtQElt]) -> MonStgElt
{Given an invertible ideal I over some order S and a basis of the algebra it returns a pair [ c,elt ] where c is the smallerst integer in I and elt is an element such that I = c*S + elt*S. Note that elt is not chosen canonically.}
    S:=Order(I);
    A:=Algebra(S);
    if I eq OneIdeal(S) then
        M:=1;
        d:=1;
        alpha:=[0 : i in [1..#basis]]; //zero of A
    else
        M:=MinimalInteger(I);
        if M*S eq I then
            d:=1;
            alpha:=[0 : i in [1..#basis]]; //zero of A
        else
            zbI:=Rows(LLL(Matrix(AbsoluteCoordinates(ZBasis(I),basis))));
            k:=0;
            stop:=false;
            repeat
                k+:=1;
                j:=0;
                repeat
                    j+:=1;
                    rndm_coeffs:=[ Random(-k,k) : i in [1..#basis] ];
                    elt_coeffs:=[ [ rndm_coeffs[i]*z : z in ElementToSequence(zbI[i]) ] : i in [1..#basis] ];
                    elt_coeffs:=[ &+[ e[i] : e in elt_coeffs] : i in [1..#basis] ];
                    elt:=SumOfProducts(elt_coeffs,basis);
                    assert elt in I;
                    stop:=Ideal(S,[A!M,elt]) eq I;
                until stop or j eq 30;
            until stop;
            d:=LCM([ Denominator(e) : e in elt_coeffs]);
            nums:=[d*e : e in elt_coeffs];
            alpha:=nums;
        end if;
    end if;
    out:="[" cat Sprintf("%o,%o,%o",M,d,alpha) cat "]";
    out:=RemoveBlanks(out);
    return out;
end intrinsic;

intrinsic FillSchema(R::AlgEtQOrd)->MonStgElt
{Given the ZFV Order of a squarefree isogeny class which is ordinary or over the prime field, it produces a string to fill the Table av_fq_weak_equivalences at https://github.com/roed314/root-unitary/blob/stage_based/postgres_schema.md. At the same time, it populates }
    A:=Algebra(R);
    isog_label:=IsogenyLabel(DefiningPolynomial(A));
    F:=PrimitiveElement(A);
    basis:=ZFVBasis(A);
    g,q:=DimensionSizeFiniteField(A); 
    require R eq Order([F,q/F]): "the given orders is not the ZFV order of the isogeny class";

    _:=WKICM(R); // this populates overorders and WKICM_bar
    assert assigned R`OverOrders;
    oo:=OverOrders(R);
    assert forall{S:S in oo|assigned S`WKICM_bar};
    oo_sort_keys:=SortKeysOrders(oo);
    ParallelSort(~oo_sort_keys,~oo);

    // orders are now sorted.
    // orders with the same index are grouped together, and already in the right order
    indices_oo:=[ oo_sort_keys[i][1] : i in [1..#oo] ];

    // We construct the labels of the orders
    labels_oo:=[];
    current_index:=indices_oo[1];
    i:=0;
    for iS->S in oo do
        N:=indices_oo[iS];
        if N eq current_index then
            i+:=1;
        else
            // we sorted we reset the counter
            i:=1;
            current_index:=N;
        end if;
        label_S:=Sprintf("%o.%o",N,i);
        Append(~labels_oo,label_S);
    end for;

    min_oo:=[];
    // Populate min_oo: in the i-th entry we put the labels of the minimal overorders of oo[i].
    // The computation is done as follows:
    // adj_mat[i,j] = 1 if oo[i] subsetneq oo[j], and 0 otherwise (the adjacency matrix of the strinct inclusion graph)
    // The transitive reduction of the the corresponding graph 
    // (which is the subgraph whose edges are the minimal inclusions) 
    // is obtained by squaring the adj_mat.
    // The minimal overorders of oo[i] are of the form oo[j] where adj_mat[i,j]=1 and (adj_mat^2)[i,j]=0
    adj_mat:=ZeroMatrix(Integers(),#oo);
    for i,j in [1..#oo] do
        if i ne j and oo[i] subset oo[j] then
            adj_mat[i,j]:=1;
        else
            adj_mat[i,j]:=0;
        end if;
    end for;
    adj_mat_sq:=adj_mat^2; 
    for i in [1..#oo] do
        min_oo_i:=[ labels_oo[j] : j in [1..#oo] | adj_mat[i,j] eq 1 and adj_mat_sq[i,j] eq 0 ];
        Append(~min_oo,min_oo_i);
    end for;

    //conductors
    O:=MaximalOrder(Algebra(R));
    condS:=[Conductor(S) : S in oo];
    condS_prime:=[ IsPrime(ff) select "t" else "f" : ff in condS ];
    condS_ind:=[Index(oo[i],condS[i]) : i in [1..#oo]];
    condO:=[O!!ff : ff in condS];
    condO_two_gens:=[ two_generating_set(ff,basis) : ff in condO ];
    condO_prime:=[ IsPrime(ff) select "t" else "f" : ff in condO ];
    condO_ind:=[Index(O,ff) : ff in condO];
    cond_classes:=[ labels_oo[Index(condO,ff)] : ff in condO ];

    output:="";
    for iS in [1..#oo] do
        S:=oo[iS];
        wkS:=WKICM_barCanonicalRepresentatives(S);
        assert #wkS eq #WKICM_bar(S);
        S`WKICM_bar:=wkS;
        wkS_sort_keys:=SortKeysWKICM_bar(S);
        ParallelSort(~wkS_sort_keys,~wkS);
        n_sing:=#SingularPrimes(S);
        if #min_oo[iS] eq 0 then //maximal order
            minimal_overorders_S:="{}";
        else
            minimal_overorders_S:="{" cat Prune(&cat[ Sprintf("%o,",m) : m in min_oo[iS] ]) cat "}";
        end if;

        N:=indices_oo[iS];
        pic_size:=#PicardGroup(S);
        multiplicator_ring:=labels_oo[iS];
        labelS:=Sprintf("%o.%o",isog_label,multiplicator_ring);
        for j in [1..#wkS] do
            I:=wkS[j];
            sort_key:=wkS_sort_keys[j];
            label:=labelS cat Sprintf(".%o",j);
            I`WELabel:=label; // populate the attribute
            

            we_number:=j;
            hnf:=my_hnf(I,basis);
            ideal_basis_numerators:="{" cat Prune(&cat[Sprintf("%o,",hnf[i]):i in [2..#hnf]]) cat "}";
            ideal_basis_denominator:=hnf[1];
            dimensions:=[sort_key[i]:i in [1..n_sing]];
            is_invertible:=(#dimensions eq 0 or &+dimensions eq n_sing) select "t" else "f";
            if is_invertible eq "t" then
            // certain things should be stored only for the wk_classes that are orders
                minimal_overorders_I:=minimal_overorders_S;
                cohen_macaulay_type:=CohenMacaulayType(S);
                conductor:=condO_two_gens[iS];
                conductor_is_Sprime:=condS_prime[iS];
                conductor_is_Oprime:=condO_prime[iS];
                conductor_Sindex:=condS_ind[iS];
                conductor_Oindex:=condO_ind[iS];
                condutor_class:=cond_classes[iS];
            else
                minimal_overorders_I:="\\N";
                cohen_macaulay_type:="\\N";
                conductor:="\\N";
                conductor_is_Sprime:="\\N";
                conductor_is_Oprime:="\\N";
                conductor_Sindex:="\\N";
                conductor_Oindex:="\\N";
                condutor_class:="\\N";
            end if;
            if #dimensions eq 0 then //maximal order
                dimensions:="{}";
            else
                dimensions:="{" cat Prune(&cat[Sprintf("%o,",d):d in dimensions]) cat "}";
            end if;
            groups:=[ Quotient(I,(1-F^d)*I) : d in [1..10]];
            // if G is trivial, AbelianInvariants returns [] instead of [1]. Go figure.
            invariants:=[ #G eq 1 select [1] else AbelianInvariants(G) : G in groups ];
            rational_invariants:="{" cat Prune(&cat[Sprintf("%o,",i):i in invariants[1]]) cat "}";
            higher_invariants:=[ "[" cat Prune(&cat[Sprintf("%o,",i):i in invariants[d]]) cat "]," : d in [2..#invariants] ];
            higher_invariants:="[" cat Prune(&cat([inv : inv in higher_invariants])) cat "]";

            line_j:=Sprintf("%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o:%o\n",label,we_number,pic_size,multiplicator_ring,isog_label,ideal_basis_numerators,ideal_basis_denominator,is_invertible,cohen_macaulay_type,dimensions,minimal_overorders_I,rational_invariants,higher_invariants,conductor,conductor_is_Sprime,conductor_is_Oprime,conductor_Sindex,conductor_Oindex,condutor_class);

            output cat:=line_j;
        end for;
    end for;
    return output;
end intrinsic;

intrinsic WELabel(I::AlgEtQIdl)->MonStgElt
{Returns the WELabel of the weak equivalence class of I, which of the form N.i.j where N.i determines the multiplicator ring of I and j is determined by the SortKey.}
    return I`WELabel;
end intrinsic;

intrinsic WELabel(I::AlgEtQOrd)->MonStgElt
{Returns the WELabel of the weak equivalence class of the order, which of the form N.i.1}
    return I`WELabel;
end intrinsic;

intrinsic LoadSchemaWKClasses(str::MonStgElt)->AlgEtQOrd
{Given the output of the schema for one isogeny class returns the order Z[F,V] with the attributes for overorders and weak equivalence classes populated.}
    lines:=[ Split(l,":") : l in Split(str)];
// each line consists of:
//  1  label,
//  2  we_number,
//  3  pic_size,
//  4  multiplicator_ring,
//  5  isog_label,
//  6  ideal_basis_numerators,
//  7  ideal_basis_denominator,
//  8  is_invertible,
//  9  cohen_macaulay_type,
//  10 dimensions,
//  11 minimal_overorders_I,
//  12 rational_invariants,
//  13 higher_invariants,
//  14 conductor,
//  15 conductor_is_Sprime,
//  16 conductor_is_Oprime,
//  17 conductor_Sindex,
//  18 conductor_Oindex,
//  19 condutor_class
    g,q,f:=LabelToPoly(lines[1][1]);
    A:=EtaleAlgebra(f);
    F:=PrimitiveElement(A);
    V:=q/F;
    basis:=ZFVBasis(A);

    zb_in_A:=function(nums,den)
        return [SumOfProducts([c/den : c in n ],basis) : n in nums ];
    end function;

    braces_to_seq_of_seqs:=function(str)
    // given a string of the form {x1,...,xn}, constructs the sequence [x1,...,xn],
    // which is used to fill an g times g upper tri matrix, 
    // whose rows are then returned (as a sequence of sequences).
        assert str[1] eq "{" and str[#str] eq "}";
        seq:=eval("[" cat str[2..#str-1] cat "]");
        T:=UpperTriangularMatrix(seq);
        return [ Eltseq(r) : r in Rows(T) ];
    end function;

    oo:=[ Order(zb_in_A(braces_to_seq_of_seqs(l[6]),eval(l[7]))) : l in lines | l[8] eq "t" ];
    oo_labels:=[ l[4] : l in lines | l[8] eq "t" ];
    oo_indices:=[ eval(Split(l,".")[1]) : l in oo_labels ];
    assert #{ x : x in oo_indices | x eq 1} eq 1; 
    O:=oo[Index(oo_indices,1)];
    assert IsMaximal(O);
    max:=Max(oo_indices);
    assert #{ x : x in oo_indices | x eq max} eq 1; 
    R:=oo[Index(oo_indices,max)];
    assert R eq Order([F,V]);
    oo_cond:=[ eval("<" cat ll[2..#ll-1] cat ">") : ll in  [ l[14] : l in lines | l[8] eq "t" ] ];
    oo_cond:=[ Ideal(O,[A!t[1]] cat zb_in_A([t[3]],t[2])) : t in oo_cond ];
    oo_min_oo:=[ Split(l[11][2..#l[11]-1], ",") : l in lines | l[8] eq "t" ];
    // note in an older version of FillSchema I put [] instead of {} in l[11].
    // the previous line is not affected by this mistake.


    R`OverOrders:=oo;
    wkR:=[];
    // in this loop we populate the attributes of each overorder and R`WKICM
    for iS in [1..#oo] do
        S:=oo[iS];
        labelS:=oo_labels[iS];
        linesS:=[ l : l in lines | l[4] eq labelS ]; 
        wkS:=[];
        S`WELabel := labelS * ".1";
        for l in linesS do
            I:=Ideal(S,zb_in_A(braces_to_seq_of_seqs(l[6]),eval(l[7])));
            I`MultiplicatorRing:=S;
            I`WELabel:=Join(Split(l[1],".")[4..6], "."); //N.i.j
            Append(~wkS,I);
            IR:=R!!I;
            IR`MultiplicatorRing:=S;
            IR`WELabel:=I`WELabel;
            Append(~wkR,IR);
        end for;
        assert2 forall{ i : i,j in [1..#wkS] | (i eq j) eq (IsWeakEquivalent(wkS[i],wkS[j])) }; //TIME consuming
        ffS:=S!!oo_cond[iS];
        assert ffS eq Conductor(S);
        min_oo_S:=[ oo[Index(oo_labels,lab)] : lab in oo_min_oo[iS] ];
        sing_pp:=[ ColonIdeal(OneIdeal(S),S!!OneIdeal(T)) : T in min_oo_S ];
        sing_pp_set:=Seqset(sing_pp);
        assert Seqset(SingularPrimes(S)) eq sing_pp_set;
        min_oo_at_primes:=[];
        for P in Setseq(sing_pp_set) do
            min_oo_P:={@ min_oo_S[i] : i in [1..#sing_pp] | sing_pp[i] eq P @};
            Append(~min_oo_at_primes,<P,min_oo_P>);
        end for;
        S`MinimalOverOrders:=min_oo_at_primes;
        S`WKICM_bar:=wkS;
        S`WKICM_barCanonicalRepresentatives:=wkS;
    end for;
    R`WKICM:=wkR;
    return R;
end intrinsic;

/*
    SetDebugOnError(true);
    AttachSpec("~/CHIMP/CHIMP.spec");
    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AbVarFq_LMFDBLabels/spec");
    _<x>:=PolynomialRing(Integers());
    f:=x^8+16;
    A:=EtaleAlgebra(f);
    R:=Order(ZFVBasis(A));
    str:=FillSchema(R);

    delete R,A;
    R:=LoadSchemaWKClasses(str);
    for S in OverOrders(R) do 
        for I in WKICM_bar(S) do 
            try 
                WELabel(I); 
            catch e 
                e; 
                IsMaximal(S); 
            end try; 
        end for; 
    end for;

    delete R;
    R:=LoadSchemaWKClasses(str);
    for I in WKICM(R) do 
        try 
            WELabel(I); 
        catch e 
            e; 
        end try; 
    end for;

*/
