##########################
# INPUT
# The input of the computation consists of the Weil polynomials h(x) with no repeated complex roots (squarefree) of all isogeny classes of abelian varieties of dimension g over the finite field FF_q for the values listed below, that are ordianry or defined over a prime field (i.e. q is prime).
#
# g=1, q in {2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47,49,53,59,61,64,67,71,73,79,81,83,89,97,101,103,107,109,113,121,125,127,128}
# g=2, q in {2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47,49,53,59,61,64,67,71,73,79,81,83,89,97,101,103,107,109,113,121,125,127,128}
# g=3, q in {2,3,4,5,7,8,9,16,25}
# g=4, q in {2,3,4}
# g=5, q in {2}
#
# For the computation of polarizations we restrict ourselves to the isogeny classes from the list above that are ordinary.
#
# The input is sorted according to how many isogeny classes we have for that pair and is stored in 
# AbVarFq_LMFDBLabels/computation/weil_poly_sqfree_ord_cs.txt
# (unsorted input is in AbVarFq_LMFDBLabels/computation/weil_poly_sqfree_ord_cs_unsorted.txt)
#
# The 3 biggest pairs <g,q> are
# <4, 4>, <3, 16>, <3, 25> with 21.248,46.552,284.484 isogeny classes, resp.
# In particular, removing <3,25> could cut the computation by (a bit less) than half.
#
# After an intial attempy, I have decided to remove <3,25> from the first run.
#
###########################

# TODO
# make a list of what each file contains, relating it to the colums of the tables
# which can be found at:
# https://github.com/roed314/root-unitary/blob/stage_based/postgres_schema.md

# here the temp data and outputs are stored
fld_comp = ~/287_abvarfq_lmfdb_recomputation/
# where all the scripts are
fld_scripts = ~/AbVarFq_LMFDBLabels/computation/
# coeffs of the input poly, sorted (see above)
# after some thinking I have decided to remove 3.25 from the first round of recomputation
#input = ${fld_scripts}weil_poly_sqfree_ord_cs.txt
#input_ord = ${fld_scripts}weil_poly_sqfree_ord.txt
input = ${fld_scripts}weil_poly_sqfree_ord_cs_no_3_25.txt
input_ord = ${fld_scripts}weil_poly_sqfree_ord_no_3_25.txt
# where to store versions used and status (see below)
my_log = ${fld_comp}my_log

input_fast_1 = ${fld_scripts}input_fast_1
input_fast_2 = ${fld_scripts}input_fast_2
input_fast_3 = ${fld_scripts}input_fast_3
input_fast_4 = ${fld_scripts}input_fast_4

input_slow_1 = ${fld_scripts}input_slow_1
input_slow_2 = ${fld_scripts}input_slow_2
input_slow_3 = ${fld_scripts}input_slow_3
input_slow_4 = ${fld_scripts}input_slow_4

# we collect here the issue from the scripts
issues_wk = ${fld_comp}issues_wk
issues_cm = ${fld_comp}issues_cm
issues_pols = ${fld_comp}issues_pols

# output of the scripts
fld_out_wk = ${fld_comp}output_wk/
fld_out_cm = ${fld_comp}output_cm/
fld_out_pols = ${fld_comp}output_pols/

degree_bounds = [4,9,25]

rm_log:
	rm ${my_log} || true

log_versions_last_commits:
	@date >> ${my_log}
	@echo "magma version:" >> ${my_log}
	@magma -b -e 'GetVersion();' >> ${my_log}
	@echo last git commit for CHIMP: >> ${my_log}
	@git -C ~/CHIMP/ log -n 1 --pretty=format:"%H" >> ${my_log}
	@echo "\nlast git commit for AlgEt:" >> ${my_log}
	@git -C ~/AlgEt/ log -n 1 --pretty=format:"%H" >> ${my_log}
	@echo "\nlast git commit for AbVarFq_LMFDBLabels:" >> ${my_log}
	@git -C ~/AbVarFq_LMFDBLabels/ log -n 1 --pretty=format:"%H" >> ${my_log}
	@echo "\n" >> ${my_log}

echo_status:
	@echo "status on:"
	@date
	@echo "number of inputs :"
	@cat ${input} | wc -l
	@echo "number of ordinary inputs :"
	@cat ${input_ord} | wc -l
	@echo "script_wk completed :"
	@ls ${fld_out_wk} | wc -l
	@echo "script_cm completed:"
	@ls ${fld_out_cm} | wc -l
	@echo "script_pols completed :"
	@ls ${fld_out_pols}av_fq_isog | wc -l

log_status:
	@echo "status on:" >> ${my_log}
	@date >> ${my_log}
	@echo "number of inputs :" >> ${my_log}
	@cat ${input} | wc -l >> ${my_log}
	@echo "number of ordinary inputs :" >> ${my_log}
	@cat ${input_ord} | wc -l >> ${my_log}
	@echo "script_wk completed :" >> ${my_log}
	@ls ${fld_out_wk} | wc -l >> ${my_log}
	@echo "script_cm completed:" >> ${my_log}
	@ls ${fld_out_cm} | wc -l >> ${my_log}
	@echo "script_pols completed :" >> ${my_log}
	@ls ${fld_out_pols}av_fq_isog | wc -l >> ${my_log}
	@echo "\n" >> ${my_log}

status:
	@make -s echo_status
	@make -s log_status

run_script_wk:
	@echo "(re)starting run_script_wk on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel -j 20 --resume --joblog ${fld_comp}joblog_wk -a ${input} magma -b fld_out:=${fld_out_wk} issues:=${issues_wk} s:={} ${fld_scripts}script_wk.m
	@echo "run_script_wk has finished on:" >> ${my_log}
	@date >> ${my_log}

clean_failed_script_wk:
	rm ~/287_abvarfq_lmfdb_recomputation/output_wk/*
	rm ~/287_abvarfq_lmfdb_recomputation/joblog_wk
	rm ~/287_abvarfq_lmfdb_recomputation/issues_wk

run_script_cm:
	@echo "(re)starting run_script_cm on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel -j 18 --resume --joblog ${fld_comp}joblog_cm -a ${input_ord} magma -b fld_out:=${fld_out_cm} issues:=${issues_cm} s:={} ${fld_scripts}script_cm.m
	@echo "run_script_cm has finished on:" >> ${my_log}
	@date >> ${my_log}

clean_failed_script_cm:
	rm ~/287_abvarfq_lmfdb_recomputation/output_cm/*
	rm ~/287_abvarfq_lmfdb_recomputation/joblog_cm
	rm ~/287_abvarfq_lmfdb_recomputation/issues_cm

# change in the parallel command input_fast_1 to all the other inputs
# input_fast_i for i =1,2,3,4
# input_slow_i for i =1,2,3,4
run_script_pols:
	@echo "(re)starting run_script_pols on:" >> ${my_log}
	@make -s log_versions_last_commits
	parallel -j 18 --memsuspend 100G --resume --joblog ${fld_comp}joblog_pols -a ${input_fast_1} magma -b fld_comp:=${fld_comp} fld_out_wk:=${fld_out_wk} fld_out_cm:=${fld_out_cm} fld_out_pols:=${fld_out_pols} issues:=${issues_pols} degree_bounds:=${degree_bounds} s:={} ${fld_scripts}script_pols.m
	@echo "run_script_pols has finished on:" >> ${my_log}
	@date >> ${my_log}

clean_failed_script_pols:
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_pol/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_we/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols/av_fq_isog/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/output_pols/allproduct/* || true
	rm ~/287_abvarfq_lmfdb_recomputation/joblog_pols || true
	rm ~/287_abvarfq_lmfdb_recomputation/issues_pols || true
