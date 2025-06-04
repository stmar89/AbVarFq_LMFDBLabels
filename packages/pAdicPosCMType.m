/* vim: set syntax=magma :*/

declare attributes AlgEtQ : pAdicPosCMType;

sparsify_CMType:=function(PHI,basis,q)
// given a CMtype PHI and a basis of the algebra, returns an element representing PHI whose coefficients
// with respect to the basis are small. The element and its coeffs with respect to basis are returned.
    b:=CMPositiveElement(PHI);
    assert b eq -ComplexConjugate(b);
    coeffs:=AbsoluteCoordinates([b],basis)[1];
    homs:=Homs(PHI);
    dim:=Dimension(Algebra(b));

    if 3 eq Max([ Abs(c) : c in coeffs ]) then
        return b,coeffs;
    end if;

    A:=Algebra(b);
    F:=PrimitiveElement(A);
    V:=q/F;
    for bc in [F-V,V-F] do
        if (not IsZeroDivisor(bc)) and bc eq -ComplexConjugate(bc) then
            b0:=b/bc;
            if forall{ h : h in homs | Re(h(b0)) gt 0 } then
                return bc,AbsoluteCoordinates([bc],basis)[1];
            end if;
        end if;
    end for;

    basis_homs:=[[ h(b) : b in AbsoluteBasis(A) ] : h in homs ];

    SS:=&cat([Setseq(Subsets({1..dim},i)) : i in [1..dim]]);
    for k in [1..3] do
        for S in SS do
            count:=0;
            cc:=CartesianProduct( [i in S select [k..-k by -1] else [0]: i in [1..dim-1]] cat [[0]] );
            count_max:=Min([100,#cc]);
            for count in [1..count_max] do
                c:=Random(cc);
                coeff:=[ c[i] : i in [1..dim] ];
                bc:=SumOfProducts(coeff,basis);
                if bc ne ComplexConjugate(bc) then
                    bc:=bc-ComplexConjugate(bc); // non zero by the "if" 
                    if not IsZeroDivisor(bc) then
                        b0:=AbsoluteCoordinates(b/bc);
                        if &and[ Re(&+[ b0[i]*basis_homs_h[i] : i in [1..dim] ]) gt 0 : basis_homs_h in basis_homs ] then
                        //b0:=b/bc;
                        //if forall{ h : h in homs | Re(h(b0)) gt 0 } then
                            coeff:=AbsoluteCoordinates([bc],basis)[1];
                            return bc,coeff;
                        end if;
                    end if;
                end if;
            end for;
        end for;
    end for;

    k:=0;
    while true do
        k+:=1;
        for S in SS do
            count:=0;
            cc:=CartesianProduct( [i in S select [k..-k by -1] else [0]: i in [1..dim]] cat [[0]] );
            count_max:=Min([100,#cc]);
            for count in [1..count_max] do
                c:=Random(cc);
                coeff:=[ c[i] : i in [1..dim] ];
                bc:=SumOfProducts(coeff,basis);
                if bc ne ComplexConjugate(bc) then
                    bc:=bc-ComplexConjugate(bc); // non zero by the "if" 
                    if not IsZeroDivisor(bc) then
                        b0:=AbsoluteCoordinates(b/bc);
                        if &and[ Re(&+[ b0[i]*basis_homs_h[i] : i in [1..dim] ]) gt 0 : basis_homs_h in basis_homs ] then
                        //b0:=b/bc;
                        //if forall{ h : h in homs | Re(h(b0)) gt 0 } then
                            coeff:=AbsoluteCoordinates([bc],basis)[1];
                            return bc,coeff;
                        end if;
                    end if;
                end if;
            end for;
        end for;
    end while;
end function;

intrinsic pAdicPosCMType(A::AlgEtQ : precpAdic := 30, precCC := 30 ) -> AlgEtQCMType
{Given an etale algebra A = Q[x]/h = Q[F], where h is a squarefree ordinary q-Weil polynomial, it returns an AlgEtCMType PHI of A such that phi(F) has positive p-adic valuation according to some fixed embedding of \barQp in C. It uses the package padictocc.m written by John Voight. }
    if assigned A`pAdicPosCMType then
        return A`pAdicPosCMType;
    end if;
    h:=ChangeRing(DefiningPolynomial(A),Integers());
    _,p:=IsPrimePower(ConstantCoefficient(h));
    require IsCoprime(Coefficients(h)[(Degree(h) div 2)+1],p) : "The isogeny class is not ordinary";
    rtspp,rtsCC:=pAdicToComplexRoots(PolynomialRing(Rationals())!h,p : precpAdic := precpAdic, precCC:=precCC );
        //from paddictocc.m. works only for ordinary
    homs:=HomsToC(A : Prec:=precCC );
    FA:=PrimitiveElement(A);
    homs_FA:=[Parent(rtsCC[1])!h(FA) : h in homs ];
    cmtype_homs:=[ ];
    for ir in [1..#homs_FA] do
        r:=homs_FA[ir];
        assert exists(ind){ irCC : irCC in [1..#rtsCC] | Abs(r-rtsCC[irCC]) lt 10^(-(precCC div 2)) };
        if Valuation(rtspp[ind]) gt 0 then
            Append(~cmtype_homs,homs[ir]);
        end if;
    end for;
    assert #cmtype_homs eq (Degree(h) div 2);
    PHI:=CMType(cmtype_homs);
    A`pAdicPosCMType:=PHI;
    return PHI;
end intrinsic;

intrinsic SaveCMType(PHI::AlgEtQCMType) -> MonStgElt
{Given a CM-Type PHI of a commutative endomorphism algebra, it returns a string representing the coefficients of a PHI-positive element b with respect to the ZFVBasis, where b is chosen in so that this coefficients are small integers. A second string is returned with the same numerical values, but with [] replaced by \{\}.}
    A:=Domain(Homs(PHI)[1]);
    basis:=ZFVBasis(A);
    _,q:=DimensionSizeFiniteField(A);
    _,coeffs:=sparsify_CMType(PHI,basis,q);
    output:=RemoveBlanks(Sprint(coeffs));
    output2:="{" * output[2..#output-1] * "}";
    return output,output2;
end intrinsic;

intrinsic LoadpAdicPosCMType(A::AlgEtQ,str::MonStgElt)->AlgEtQCMType
{Given a commutative endomorphisgma algebra and  string produced by SaveCMType, it loads the corresponing CM-Type. The CM-Type is supposed to be p-adic positive since it populates A`pAdicPosCMType..}
    basis:=ZFVBasis(A);
    str:=str[2..#str-1];
    str:=[ StringToInteger(s) : s in Split(str,",") ];
    b:=SumOfProducts(str,basis);
    assert b eq -ComplexConjugate(b);
    PHI:=CMType(b);
    A`pAdicPosCMType:=PHI;
    return pAdicPosCMType(A);
end intrinsic;


