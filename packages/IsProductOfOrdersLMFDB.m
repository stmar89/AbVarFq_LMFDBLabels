/* vim: set syntax=magma :*/

declare attributes AlgEtQOrd : IsProductOfOrdersLMFDB;

intrinsic IsProductOfOrdersLMFDB(S::AlgEtQOrd)->BoolElt,SeqEnum[AlgEtQElt],SeqEnum
{Returns whether S is a product of orders S1 x .. x Sn for orders Si in some factor algebra of Algebra(S), together with the idempotents ei of Algebra of S such that Si=ei*S, and the product_partition as a list of lists of integers, giving which components of the etale algebra which are clustered together. For example: [[1,2,...,m]] means that there is no splitting; [[1],[2],...,[m]] means that S is a product of integral domains. Here m is the number of components of the etale algebra, and the components are ordered by sorting their defining polynomials.}
    if not assigned S`IsProductOfOrdersLMFDB then
        A:=Algebra(S);
        idem:=[ i : i in Idempotents(A) | i in S]; // idempotents in S
        output:=[PowerStructure(AlgEtQElt)|];
        if Seqset(idem) eq { One(A), Zero(A) } then
            return false,output,[[i : i in [1..#Components(A)]]];
        end if;

        test,D:=IsPowerOf(#idem,2);
        assert test;
        F2:=GF(2);
        V:=VectorSpace(F2,#Components(A));
        idem_inV:=[ V![ c eq 1 select F2!1 else F2!0 : c in Components(i) ] : i in idem ];
        arr:=AssociativeArray();
        for j in [1..#idem] do
            i:=idem[j];
            v:=idem_inV[j];
            n:=#[ x : x in Eltseq(v) | x eq 1 ];
            if not IsDefined(arr,n) then
                arr[n]:=[];
            end if;
            Append(~arr[n],j);
        end for;
        max:=Max(Keys(arr));
        W:=sub<V|>;
        n:=1;
        while Dimension(W) lt D do
            if IsDefined(arr,n) then
                for j in arr[n] do
                    v:=idem_inV[j];
                    if not v in W then 
                        Append(~output,idem[j]);
                        W:=sub<V| W,v>;
                        if Dimension(W) eq D then
                            break;
                        end if;
                    end if;
                end for;
            end if;
            n+:=1;
        end while;
        assert #output eq D;
        assert OneIdeal(S) eq Ideal(S , [ z*g : z in ZBasis(S) , g in output ]);

        // LMFDB
        // we now compute the product partition
        prod_part:=[];
        nfs:=[ Coefficients(DefiningPolynomial(K)) : K in Components(A) ];
        require #nfs eq #Seqset(nfs) : "We need the number fields forming the etale algebra to be different";
        ind:=[1..#nfs];
        ParallelSort(~nfs,~ind);
        for id in output do
            comp:=Components(id);
            comp:=[ comp[ind[i]] eq 1 select 1 else 0 : i in [1..#ind] ]; //sorted
            Append(~prod_part,[ i : i in [1..#ind] | comp[i] eq 1 ]); 
        end for;
        S`IsProductOfOrdersLMFDB:=<true, output, prod_part>; 
    end if;
    return Explode(S`IsProductOfOrdersLMFDB);
end intrinsic;

/*
    SetDebugOnError(true);
    AttachSpec("~/CHIMP/CHIMP.spec");
    AttachSpec("~/AlgEt/spec");
    AttachSpec("~/AbVarFq_LMFDBLabels/spec");

    _<x>:=PolynomialRing(Integers());
    f:=(x^2-2)*(x^2-3)*(x^2-5);
    A:=EtaleAlgebra(f);
    E:=EquationOrder(A);
    assert not IsProductOfOrdersLMFDB(E);
    O:=MaximalOrder(A);
    assert IsProductOfOrdersLMFDB(O);
    oo:=FindOverOrders(E);
    for S in oo do
        IsProductOfOrdersLMFDB(S);
    end for;

*/
