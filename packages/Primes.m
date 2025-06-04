/* vim: set syntax=magma : */
/*

*/
    
declare attributes AlgEtQIdl : SortKey; //See SortKeyPrime for a description.

declare attributes AlgEtQOrd : SingularPrimesSorted;  // singular primes of the order, according to the their SortKey.

intrinsic SortKeyPrime(P::AlgEtQIdl)->SeqEnum[RngIntElt]
{Given a P of the maximal order of an etale algebra K over Q, returns a sequence of 3 integers [ j , N , i ], in the following way:
- Write K = K1 x ... x Kn where the Ki's are number fields sorted according to the lexicographic order of the coefficients of the defining polynomial, starting from the constant term.
- Write P as a direct sum of n ideals, according to the same order. Only one, the jth, of these direct summands does not contain the unique element. More precisely, if Pi denotes the i-th direct summand of P then Pi=OKi for all i ne j and Pj is a prime of OKj.
- Finally, N.i is the LMFDB label of Pj.
If P is a prime of a non-maximal order, then the output is the smallest sortkey of the finitely many primes of the maximal order OK above P, sorted lexicographically according to the [j,N,i]-scheme defined above. Note that if PP is an ideal of OK above P, then PP meet Order(P) = P. 
Important: we assume that the number fields forming the etale algebra are different.}
    if not assigned P`SortKey then
        S:=Order(P);
        A:=Algebra(S);
        if IsMaximal(S) then
            require IsPrime(P) : "The ideal is not prime";
            nfs:=[ Coefficients(DefiningPolynomial(K)) : K in Components(A) ];
            require #nfs eq #Seqset(nfs) : "We need the number fields forming the etale algebra to be different";
            ind:=[1..#nfs];
            // we sort the number fields
            ParallelSort(~nfs,~ind);
            _,Ps:=IsProductOfIdeals(P);
            // we sort the component of P in the same way
            Ps:=< Ps[ind[i]] : i in [1..#ind] >;
            j:=[ i : i in [1..#nfs] | not One(Order(Ps[i])) in Ps[i] ][1];
            P_lmfdb:=LMFDBLabel(Ps[j]);
            P_lmfdb:=[ eval(s) : s in Split(P_lmfdb,".") ];
            assert #P_lmfdb eq 2;
            // we construct the sortkey
            P`SortKey:=[ j ] cat P_lmfdb;
        else
            O:=MaximalOrder(A);
            // we consider the primes above P
            pp:=PrimesAbove(O!!P);
            require forall{Q : Q in pp | (OneIdeal(S) meet S!!Q) eq P} : "The ideal is not prime";
            // and pick the on with smallest sort-key
            P`SortKey:=Min([ $$(Q) : Q in pp ]);
        end if;
    end if;
    return P`SortKey;
end intrinsic;

intrinsic SortPrimes(seq::SeqEnum[AlgEtQIdl]) -> SeqEnum[AlgEtQIdl]
{Given a sequence of primes of an order S, it sorts the sequence according to the lexicographic order of their SortKey.}
    keys:=[ SortKeyPrime(P) : P in seq ];
    ParallelSort(~keys,~seq);
    return seq;
end intrinsic;

intrinsic ComparePrimes(P::AlgEtQIdl,Q::AlgEtQIdl) -> RngIntElt 
{It returns -1 if P < Q, 0 if P eq Q, and 1 if P > Q, where the ordering is determined by the lexicographic order of their SortKeys.}
    require Order(P) eq Order(Q) : "The input ideals must be primes of the same order";
    if P eq Q then
        return 0;
    else
        P:=SortKeyPrime(P);
        Q:=SortKeyPrime(Q);
        if P lt Q then
            return -1;
        else 
            return 1;
        end if;
    end if;
end intrinsic;

intrinsic SortSingularPrimes(S::AlgEtQOrd) -> SeqEnum[AlgEtIdl]
{It sorts the singular primes of the order S according the lexicographic order of their sort keys.}
    if not assigned S`SingularPrimesSorted then
        if IsMaximal(S) then
            S`SingularPrimesSorted:=[PowerStructure(AlgEtQIdl)|];
        else
            S`SingularPrimesSorted:=SortPrimes(SingularPrimes(S));
        end if;
    end if;
    return S`SingularPrimesSorted;
end intrinsic;

/*

    

*/
