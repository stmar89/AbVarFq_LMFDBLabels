/* vim: set syntax=magma : */
/* IMPORTANT: this does the compuation up-to twis. Not sure we want that.  */
TODO need to use FillSchema on ZFV to produce the string.

/*
    variables:
        fld = current folder
        fld_out = output folder
        fld_out_twist = output folder for twists
        issue_file = where the issues are recorded
        s = string of integers, eg [ 101, -20, 1 ] 

    polynomials are only up to twists

*/
    
    AttachSpec(fld cat "AlgEt/spec");
    Attach(fld cat "AlgEt/dev/rec_wk_icm.m");
    P<x>:=PolynomialRing(Integers());
       

    function twist_seq(S,pows_F,pows_Ft)
    // given a seq of elets of A, a seq pows_F=[ 1 , F , F^2 ,... ] where F:=PrimitiveElement(A)
    // we change the signs of the coeffs of F^i with i odd.
        seq:=ZBasis(S);
        coord:=AbsoluteCoordinates(seq,pows_F);
        return [&+[ IsOdd(i) select c[i]*pows_Ft[i] else -c[i]*pows_Ft[i] : i in [1..#c] ] : c in coord ];
    end function;

    function twist_wkicm(R,ft)
        At:=EtaleAlgebra(ft);
        q:=Integers() ! Truncate( ConstantCoefficient(ft)^(2/Degree(ft)) );
        Ft:=PrimitiveElement(At);
        Rt:=Order([Ft,q/Ft]);
        F:=PrimitiveElement(Algebra(R));
        dim:=Degree(ft);
        pows_F:=[ F^i : i in [0..dim-1] ];
        pows_Ft:=[ Ft^i : i in [0..dim-1] ];
            
        oo:=FindOverOrders(R);
        oot:=[ ];
        for iS->S in oo do
            St:=Order(twist_seq(S,pows_F,pows_Ft));
            wkS:=WKICM_bar(S);
            wkSt:=[Ideal(St,twist_seq(I,pows_F,pows_Ft)) : I in wkS ];
            St`WKICM_bar:=wkSt;
            Append(~oot,St);
        end for;
        assert #oo eq #oot;
        Rt`OverOrders:=oot;
        return Rt;
    end function;

    try 
        f:=P!eval(s);
        A:=EtaleAlgebra(f);
        F:=PrimitiveElement(A);
        q:=Integers() ! Round(ConstantCoefficient(f)^(2/Degree(f)));
        R:=Order([F,q/F]);
        t0:=Cputime();
        wk:=#WKICM(R);
        str:=PrintWKICM(R);
        label:=IsogenyLabel(f);
        printf "\n\tsec=%o\twk=%o\tf=%o",Cputime(t0),wk,label;
        fprintf fld_out cat label cat "_wkicm.txt","%o",str;
    catch e
        e;
        fprintf issue_file,"%o\n%o\n\n",s,e;
    end try;
    try
        // twist
        ft:=Evaluate(f,-x);
        if ft ne f then
            Rt:=twist_wkicm(R,ft);
            strt:=PrintWKICM(Rt);
            labelt:=IsogenyLabel(ft) cat "_wkicm.txt";        
            fprintf fld_out_twist cat labelt cat "_wkicm.txt","%o",strt;
        end if;
    catch e
        e;
        fprintf issue_file,"%o twist\n%o\n\n",s,e;
    end try;
    quit;

