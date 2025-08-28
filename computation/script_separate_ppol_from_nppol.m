/* vim: set syntax=magma :*/

/*

    On babbage we had a computation running. it used old code to compute non-principal polarizations.
    the purpose of this script is to take the data about principal polarizations and put it in the right folder.

    20250828: during a non careful migration from diophantus I have readded data about non-pp in some files.
    I modified the script below to fix that.
    
*/

    // // where the files produced with the old code are:
    // fld_old_code:="~/287_abvarfq_lmfdb_recomputation/output_pols_using_old_code/av_fq_pol/";
    // // where we are going to print the lines about pp's:
    // fld_dest_pp:="~/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_pol/";
    fld_old_code:="/data/stmar/287_abvarfq_lmfdb_recomputation/output_after_broken_rsync/av_fq_pol/";
    fld_dest_pp:="/data/stmar/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_pol/";
    file_list:=Split(Pipe("ls " * fld_old_code,"r"));
    
    tot:=#file_list; perc:=0; num_pol:=0; num_pp:=0;
    for i->file in file_list do
        if Truncate(i*100/tot) gt perc then perc+:=1; printf "%o%% %o %o\n",perc,num_pp,num_pol; end if;
        file_output:=fld_dest_pp * file;
        lines:=Split(Read(fld_old_code * file));
        for l in lines do
            num_pol+:=1;
            label:=Split(l,":")[1]; // label of form g.q.coeff-N.i.w.j-d.k
            split:=Split(label,"-.");
            assert #split eq 9;
            d:=split[8];
            assert d in {"1","4","9","25"};
            if d eq "1" then
                num_pp+:=1;
                fprintf file_output,"%o\n",l;
                //printf "%o\n",l;
            end if;
        end for;
    end for;

    quit;



