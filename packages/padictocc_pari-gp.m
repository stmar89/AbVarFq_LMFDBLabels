/* vim: set syntax=magma :*/

//freeze;
 
declare verbose padictocc,1;

// The next intrinsic is a version of the one contained in padictocc.m but we compute the SplittingField and IsSquare by invocking pari-gp, which is much faster at these things.

intrinsic pAdicToComplexRoots(f::RngUPolElt[FldRat], p::RngIntElt : precpAdic := 0, precCC := 0) -> 
    SeqEnum[RngPadElt], SeqEnum[FldComElt]
  {Returns the ordered set of roots of f p-adically and over the complex numbers
   such that the natural bijection arises from roots in a splitting field over 
   the rationals.  The varargs precpAdic and precCC specify (minimum) output 
   padic and complex precision.}

    n := Integers()!(Degree(f)/2);
    R<x> := PolynomialRing(Rationals());
    _, q := IsPower(Coefficient(f,0),n);
    assert q eq p^(Valuation(q,p));
    Rf := quo<R | f>;
    fred := Sqrt(CharacteristicPolynomial(Rf.1 + q/Rf.1));
    vprintf padictocc : "Computing Splitting Field ...";
    // we do the next one with gp
    // F := SplittingField(fred);
    // if Degree(F) eq 1 then
    //     F := RationalsAsNumberField();
    // end if;
    // vprintf padictocc : "Computing Roots of fred in F ...";
    // rtsF := Roots(fred,F);
    // vprintf padictocc : "done\n";
    // assert {r[2] : r in rtsF} eq {1}; // squarefree condition
    // rtsF := [r[1] : r in rtsF];
    vprintf padictocc : "with pari-gp...";
        cmd := Sprintf(
               "{
               h = Pol(Vecrev(%o),'x); 
               M = nfsplitting(h,%o);
               rtsM = concat([ nfisincl(g,M) | g<-Vec(factor(h,1))[1] ]);
               print1([Vecrev(M),[ Vecrev(t) | t<-rtsM ]])
               }",
               Coefficients(fred),#GaloisGroup(fred)); // Addding the deg of the splitting fields
                                                       // Speeds up the computation
                                                       // Note: nfisincl is vastly faster than nffactor
        //time s := Pipe("gp -q -D timer=0", cmd);
        time s := Pipe("sage -gp -q -D timer=0", cmd);
        s := eval("<" cat s[2..#s-2] cat ">");
        F:=NumberField(Parent(fred)!s[1]);
        if Degree(F) eq 1 then
            F := RationalsAsNumberField();
        end if;
        rtsF:=[ F ! (r cat [ 0 : i in [1..Degree(F)-#r] ]) : r in s[2]]; 
                        // the output of pari might have less coefficients 
                        // if the one of highest degree are =0
        assert #rtsF eq Degree(fred);
        assert forall{r:r in rtsF|Evaluate(fred,r) eq 0};
    // end of pari stuff
    vprintf padictocc : "done\n";

    if precpAdic eq 0 then
        ZZp := pAdicRing(p);
    else
        ZZp := pAdicRing(p,precpAdic);
    end if;
    try
        Kp := FieldOfFractions(SplittingField(f,ZZp));  // returns a ring, go figure!
    catch e
    // insufficient padic precision
        prec := Max(precpAdic,20);
        success := false;
        repeat
          prec +:= 20;
          ZZp := pAdicRing(p,prec);
          try
            vprintf padictocc : "Computing SplittingField of f over ZZp at precision %o ...",prec;
            Kp := FieldOfFractions(SplittingField(f,ZZp));  // returns a ring, go figure!
            vprintf padictocc : "done\n";
            success := true;
          catch e;
            vprintf padictocc : "precision prec=%o is not enough\n",prec;
          end try;
        until success;
    end try;    

    // for each root alpha of fred, we have two roots beta of f satisfying
    // beta^2 - alpha*beta + q = 0  [since beta + q/beta = alpha]
    // let d = disc = alpha^2-4*q; 
    // we need to keep track of the square classes of the discriminants,
    // when we see a new one we choose an embedding, when we have an old
    // one we use previous embedddings
    rtsCC := [];
    rtsp := [];
    alpha1 := rtsF[1];
    K1 := ext<F | Polynomial([q,-alpha1,1])>;
    Ks := [K1];
    v1 := InfinitePlaces(K1)[1];
    vs := [* v1 *];
    vprintf padictocc : "Computing Roots 1 ...";
    mu1p := [r[1] : r in Roots(MinimalPolynomial(F.1),Kp)][1];  // take first one, it's a choice
    vprintf padictocc : "done\n";
    mF1p := map<F -> Kp | u :-> &+[(F!u)[i+1]*mu1p^i : i in [0..Degree(F)-1]]>;
    assert IsWeaklyZero(Evaluate(MinimalPolynomial(F.1),mF1p(F.1))); // sanity check
    vprintf padictocc : "Computing Roots 2 ...";
    beta1p := [r[1] : r in Roots(Polynomial([q,-mF1p(alpha1),1])) | Valuation(r[1]) eq 0][1];
    vprintf padictocc : "done\n";
    mK1qq := map<K1 -> Kp | u :-> mF1p((K1!u)[1]) + mF1p((K1!u)[2])*beta1p>;
    qqs := [* mK1qq *];
    Append(~rtsp, beta1p);
    if precCC eq 0 then
        beta1CC := Evaluate(K1.1, v1); // use default
    else
        beta1CC := Evaluate(K1.1, v1 : Precision := precCC);
    end if;
    Append(~rtsCC, beta1CC);
    embedded_discs := [<alpha1^2-4*q, beta1CC-q/beta1CC, beta1p-q/beta1p>];
    // first one is arbitrary, guaranteed to be irreducible because has complex place
    vprintf padictocc : "#embedded_discs=%o\n",#embedded_discs;

    for j := 2 to n do
        vprintf padictocc : "in for loop %o/%o:\n",j,n;
        alphaj := rtsF[j];
        dj := alphaj^2-4*q;
        embfound := false;
        for dexps in CartesianPower([0,1],#embedded_discs) do
            vprintf padictocc : "\tnew dexp:\n";
            ed := &*[embedded_discs[i][1]^dexps[i] : i in [1..#dexps]];
            vprintf padictocc : "\t\tcomputed ed\n";
            // we do the next line with pari-gp
            // bl, csq := IsSquare(dj/ed);
                vprintf padictocc : "Computing IsSquare... with pari-gp...";
                elt:=dj/ed;
                /*
                cmd := Sprintf(
                       "{
                       h = Pol(Vecrev(%o),'a); 
                       F = nfinit(h);
                       elt = Mod(Pol(Vecrev(%o),'a),h);
                       bl = nfeltissquare(F, elt , &y);
                       print1([ bl , Vecrev(y) ])
                       }",
                       Coefficients(DefiningPolynomial(F)),Eltseq(elt));
                */
                // but the function nfeltissquare is bugged. below there is a workaround.
                cmd := Sprintf(
                       "{
                       h = Pol(Vecrev(%o),'a); 
                       F = nfinit(h);
                       elt = Mod(Pol(Vecrev(%o),'a),h);
                       g = Pol([1,0,-elt],'x);
                       rr = nfroots(F,g);
                       if(#rr>0,print1([ 1 , Vecrev(lift(rr[1])) ]),print1([ 0 , 0 ]));
                       }",
                       Coefficients(DefiningPolynomial(F)),Eltseq(elt));
                //time s := Pipe("gp -q -D timer=0", cmd);
                time s := Pipe("sage -gp -q -D timer=0", cmd);
                bl , csq := Explode(eval("<" cat s[2..#s-2] cat ">"));
                bl := bl eq 1;
                vprintf padictocc : "\t\tbl=%o\n",bl;
                if bl then
                    csq:=F ! (csq cat [ 0 : i in [1..Degree(F)-#csq] ]); 
                    assert csq^2 eq elt;
                end if;
            // end of pari-gp part
            if bl then
                // can use existing embedding: betaj = (alphaj + sqrt(d_j))/2
                // so sqrt(d_j) = csq*sqrt(ed), so to speak
                dv := &*[embedded_discs[i][2]^dexps[i] : i in [1..#dexps]];
                dqq := &*[embedded_discs[i][3]^dexps[i] : i in [1..#dexps]];
                betajp := (mF1p(alphaj)+mF1p(csq)*dqq)/2;
                betajCC := (Evaluate(alphaj,v1) + Evaluate(csq,v1)*dv)/2;
                if Valuation(betajp) gt 0 then
                    betajp := q/betajp;
                    betajCC := q/betajCC;
                end if;
                assert Valuation(betajp) eq 0;
                Append(~rtsp, betajp);
                Append(~rtsCC, betajCC);
                embfound := true;
                break;
            end if;
        end for;
        vprintf padictocc : "\t\nembfound=\n",embfound;
        if not embfound then
            Kj := ext<F | Polynomial([q,-alphaj,1])>;
            Append(~Ks, Kj);
            vj := InfinitePlaces(Kj)[1];
            Append(~vs, vj);
            vprintf padictocc : "\tComputing Roots 3 ...";
            betajp := [r[1] : r in Roots(Polynomial([q,-mF1p(alphaj),1])) | Valuation(r[1]) eq 0][1];
            vprintf padictocc : "done\n";
            mKjqq := map<Kj -> Kp | u :-> mF1p((Kj!u)[1]) + mF1p((Kj!u)[2])*betajp>;
            Append(~qqs, mKjqq);
            Append(~rtsp, betajp);
            if precCC eq 0 then
                betajCC := Evaluate(Kj.1, vj); // use default
            else
                betajCC := Evaluate(Kj.1, vj : Precision := precCC);
            end if;
            Append(~rtsCC, betajCC);
            Append(~embedded_discs, <alphaj^2-4*q, betajCC-q/betajCC, betajp-q/betajp>);
        end if;
        vprintf padictocc : "done\n";
    end for;  
  
  return rtsp cat [q/r : r in rtsp], rtsCC cat [q/r : r in rtsCC];
end intrinsic;
