/* vim: set syntax=magma :*/

declare attributes AlgEtQ : pAdicPosCMType;

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
