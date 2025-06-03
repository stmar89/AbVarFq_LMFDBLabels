


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
# The input is stored in 
# AbVarFq_LMFDBLabels/computation/weil_poly_sqfree_ord_cs.txt
#
# TODO do we do non-princ pols for all of them?
#
###########################
#
# We split the computation in TODO different steps with some dependencies between them.
# Here is a summary.
# 

# TODO update below

fld = ~/266_wk_icm_rec/
fld_out = ${fld}output/
fld_out_twist = ${fld}output_twist/
input_slow = ${fld}weil_poly_sqfree_slow.txt
input_up_to_twist = ${fld}weil_poly_sqfree_up_to_twist.txt
input_up_to_twist_sorted = ${fld}weil_poly_sqfree_up_to_twist_sorted.txt
joblog_wkicm = ${fld}joblog_wkicm.txt
issue_file = ${fld}issue_wkicm.txt
issue_file_test_wk_eq = ${fld}issue_test_wk_eq.txt
issue_file_test_wk_complete = ${fld}issue_test_wk_complete.txt
status_file = ${fld}status_wkicm.txt

all: echo_status_init parallel echo_status 

copy_packages:
	@echo "Removing old AlgEt..."
	rm -r ${fld}AlgEt || true
	mkdir ${fld}AlgEt
	mkdir ${fld}AlgEt/AlgEtQ
	mkdir ${fld}AlgEt/dev
	@echo "...Done\nCopying AlgEt..."
	cp ~/packages_github/AlgEt/AlgEtQ/*.m ${fld}AlgEt/AlgEtQ/
	cp ~/packages_github/AlgEt/dev/rec_wk_icm.m ${fld}AlgEt/dev/
	cp ~/packages_github/AlgEt/spec ${fld_isog_data}AlgEt/
	@echo "...Done"

prep_input:
	@echo "We take all squarefree Weil polynomials and put the slow one at the end.."
	magma -b fld:=${fld} weil_sqfree_slow:=${input_slow} weil_sqfree_up_to_twist:=${input_up_to_twist} weil_sqfree_up_to_twist_sorted:=${input_up_to_twist_sorted} ${fld}prep_input.txt
	@echo "...Done"

clean_failed_parallel:
	@echo "Cleaning up.."
	rm -r ${fld_out} || true
	mkdir ${fld_out}
	rm -r ${fld_out_twist} || true
	mkdir ${fld_out_twist}
	rm ${joblog_wkicm} || true
	rm ${issue_file} || true
	rm ${status_file} || true
	@echo "...Done"

parallel:
	@echo "Parallel is starting.."
	parallel -j 10 --resume --joblog ${joblog_wkicm} -a ${input_up_to_twist_sorted} magma -b fld:=${fld} fld_out:=${fld_out} fld_out_twist:=${fld_out_twist} issue_file:=${issue_file} s:={} ${fld}parallel_wkicm.txt
	@echo "...Done"

echo_status_init:
	@date >> ${status_file}
	@echo "input :" >> ${status_file}
	@cat ${input_up_to_twist_sorted} | wc -l >> ${status_file}
	@echo "completed (off by one):" >> ${status_file}
	@cat ${joblog_wkicm} | wc -l >> ${status_file}
	@echo "issues found:" >> ${status_file}
	@cat ${issue_file} | wc -l >> ${status_file} || true
	@echo "" >> ${status_file}
	@cat ${status_file}

echo_status:
	@date >> ${status_file}
	@echo "input :" >> ${status_file}
	@cat ${input_up_to_twist_sorted} | wc -l >> ${status_file}
	@echo "completed (off by one):" >> ${status_file}
	@cat ${joblog_wkicm} | wc -l >> ${status_file}
	@echo "issues found:" >> ${status_file}
	@cat ${issue_file} | wc -l >> ${status_file} || true
	@echo "" >> ${status_file}
	@cat ${status_file}
	magma -b fld:=${fld} out_fld:=${fld_out} inp:=${input_up_to_twist_sorted} joblog_file:=${joblog_wkicm} parse_joblog.txt

test_wk_eq:
	magma -b fld:=${fld} fld_out:=${fld_out} issue_file:=${issue_file_test_wk_eq} test_output_wk_eq.txt

test_wk_complete:
	magma -b fld:=${fld} fld_out:=${fld_out} issue_file:=${issue_file_test_wk_complete} test_output_complete.txt



