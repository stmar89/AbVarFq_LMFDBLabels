/* vim: set syntax=magma : */
/*

*/

declare attributes AlgEtQ : DimensionSizeFiniteField;

//////////////////////
// String manipulation
//////////////////////

intrinsic RemoveBlanks(str::MonStgElt) -> MonStgElt
{Given a string str removes the blank spaces}
    return &cat(Split(str," "));
end intrinsic;

intrinsic remove_whitespace(X::MonStgElt) -> MonStgElt
{ Strips spaces and carraige returns from string; much faster than StripWhiteSpace. }
    return Join(Split(Join(Split(X," "),""),"\n"),"");
end intrinsic;

intrinsic sprint(X::.) -> MonStgElt
{ Sprints object X with spaces and carraige returns stripped. }
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return remove_whitespace(Sprintf("%o",X));
end intrinsic;

//////////////////////
// Hermite Normal Form variant
//////////////////////

intrinsic my_hnf(I::AlgEtQOrd,basis::SeqEnum[AlgEtQElt]) -> SeqEnum[RngIntElt]
{Given an order in an etale algebra A of dimension N over Q, and a Q-basis basis of A, it returns a sequence of integers [ den ] cat T where:
- T are the g(g+1)/2 entries of a gxg upper triangular matrix, and
- (1/den)*T is the HNF of the matrix representing any ZBasis of I with respect to basis.}
    M:=Matrix(AbsoluteCoordinates(ZBasis(I),basis));
    N:=Nrows(M);
    den:=Denominator(M);
    M:=ChangeRing(den*M,Integers());
    M:=HermiteForm(M);
    out:=[den];
    for i in [1..N] do
        for j in [i..N] do
            Append(~out,M[i,j]);
        end for;
    end for;
    ChangeUniverse(~out,Integers());
    return out;
end intrinsic;

intrinsic my_hnf(I::AlgEtQIdl,basis::SeqEnum[AlgEtQElt]) -> SeqEnum[RngIntElt]
{Given a fractional ideal over some order in an etale algebra A of dimension N over Q, and a Q-basis basis of A, it returns a sequence of integers [ den ] cat T where:
- T are the g(g+1)/2 entries of a gxg upper triangular matrix, and
- (1/den)*T is the HNF of the matrix representing any ZBasis of I with respect to basis.}
    M:=Matrix(AbsoluteCoordinates(ZBasis(I),basis));
    N:=Nrows(M);
    den:=Denominator(M);
    M:=ChangeRing(den*M,Integers());
    M:=HermiteForm(M);
    out:=[den];
    for i in [1..N] do
        for j in [i..N] do
            Append(~out,M[i,j]);
        end for;
    end for;
    ChangeUniverse(~out,Integers());
    return out;
end intrinsic;

//////////////////////
// g and q from AlgEt
//////////////////////

intrinsic DimensionSizeFiniteField(A::AlgEtQ)->RngIntElt,RngIntElt
{Given a commutative endomorpshim algebra A of some isogeny class of dimension g over Fq, it returns g,q.}
    if not assigned A`DimensionSizeFiniteField then
        g:=Dimension(A) div 2;
        q:=Round(ConstantCoefficient(DefiningPolynomial(A))^(1/g));
        A`DimensionSizeFiniteField:=<g,q>;
    end if;
    return Explode(A`DimensionSizeFiniteField);
end intrinsic;

//////////////////////
// IsogenyLabels
//////////////////////

function Base26Encode(n)
        alphabet := "abcdefghijklmnopqrstuvwxyz";
        s := alphabet[1 + n mod 26]; n := ExactQuotient(n-(n mod 26),26);
        while n gt 0 do
                s := alphabet[1 + n mod 26] cat s; n := ExactQuotient(n-(n mod 26),26);
        end while;
        return s;
end function;

function Base26Decode(s)
        alphabetbase := StringToCode("a");
        n := 0;
        for c in Eltseq(s) do n := 26*n + StringToCode(c) - alphabetbase; end for;
        return n;
end function;

intrinsic IsogenyLabel(f::RngUPolElt) -> MonStgElt
{returns the LMFDB label of the isogeny class determined by f.}
    g:=Degree(f) div 2;
    q:=Integers() ! (Coefficients(f)[1]^(2/Degree(f)));
    str1:=Reverse(Prune(Coefficients(f)))[1..g];
    str2:="";
    for a in str1 do
        if a lt 0 then
            str2:=str2 cat "a" cat Base26Encode(-a) cat "_";
            else
            str2:=str2 cat Base26Encode(a) cat "_";
        end if;
    end for;
    str2:=Prune(str2);
    isog_label:=Sprintf("%o.%o.",g,q) cat str2;
    return isog_label;
end intrinsic;

intrinsic LabelToPoly(lab::MonStgElt) -> RngIntElt,RngIntElt,RngUPolElt
{given a an isogeny label g.q.xxx returns the integers g and q and the Weil polynomial}
    PP:=PolynomialRing(Integers());
    lab:=Split(lab,".");
    g:=eval(lab[1]);
    q:=eval(lab[2]);
    coeffs:=Split(lab[3],"_");
    out:=[1]; //the coeff of x^2g
    for cc in coeffs do
        if #cc gt 1 then
            if cc[1] eq "a" then
                Append(~out,-Base26Decode(cc[2..#cc]));
            else
                Append(~out,Base26Decode(cc));
            end if;
        else
            Append(~out,Base26Decode(cc));
        end if;
    end for;
    assert #out eq g+1;
    out2:=[ q^(g-(i-1))*out[i] : i in [1..g] ];
    out cat:= Reverse(out2);
    Reverse(~out);
    f:=PP ! out;
    return g,q,f;
end intrinsic;

