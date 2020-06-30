AIMC FINAL PROJECT
Loes Dekker (s1850024) and Rintse van de Vlasakker (s1903748)

Transaction reduction pins2pins layer using cartesian vectors described in
Golan-Gueta, Guy & Flanagan, Cormac & Yahav, Eran & Sagiv, Mooly. (2007).
Cartesian Partial-Order Reduction. 4595. 95-112. 10.1007/978-3-540-73370-6_8.

Implementation decisions:
- 	To speed up commutativity checks, all the possible concatenations of the CVs
	are also stored. These concatenations are updated whenever a CV is extended.
-	We implemented 2 schedulers for choosing the next CV to extend:
		+ Round robin
		+ Depth first (extend CV until no longer possible)
	To switch between these, the first line in the main while of tr_next_all
	must be altered.
-	We keep track of which processes are currently blocked, and consider a process
	unextendable when it unblocks another process. This ensures that deadlocks
	are retained when such a scenario is encountered.
- 	For more specifics, see the comments in tr.c

TODOs:
-	Performance optimisations of the various steps in the calc_CV() algorithm.
		+ Store the states required to check non-last commutativity, so they
		  don't have to be recalculated when updating the concatenations.
		+ Many more, most likely.
-	Implement non-determinism support.
- 	Ensure blocking is handled properly throughout the tr layer. We have not had
	much time or examples to test on. We think it works currently, but there
	may definitely be optimisations.
-	Verify the local properties in all prefixes of the CVs of emitted processes.
-	More extensive experimentation with more types of schedulers.

PERFORMANCE TESTING RESULTS
								Peterson2
===================================================================
Reduction		Time		States		Transitions		Memory (MB)
No reduction	0.000		156			272				0.01
DF CVs			0.010		48			73				0.00
RR CVs			0.000		39			58				0.00
===================================================================

								Peterson3
===================================================================
Reduction		Time		States		Transitions		Memory (MB)
No reduction	0.080		17523		47004			1.27
DF CVs			0.260		5443		13941			0.39
RR CVs			0.530		11711		30420			0.85
===================================================================

								Peterson4
===================================================================
Reduction		Time		States		Transitions		Memory (MB)
No reduction	5.760		3624214		13150952		345.63
DF CVs			77.690		998100		3501248			95.19
RR CVs			153.880		2783752		10013751		265.48
===================================================================

								X509
===================================================================
Reduction		Time		States		Transitions		Memory (MB)
No reduction	0.120		3204		12011			1.19
DF CVs			0.070		9028		35999			3.34
RR CVs			0.100		2770		9193			1.02
===================================================================

								Dbm
===================================================================
Reduction		Time		States		Transitions		Memory (MB)
No reduction	0.040		5112		20476			0.90
DF CVs			0.060		2326		8177			0.41
RR CVs			0.060		2326		8177			0.41
===================================================================

								Test3
===================================================================
Reduction		Time		States		Transitions		Memory (MB)
No reduction	0.000		99			167				0.00
DF CVs			0.000		42			55				0.00
RR CVs			0.000		47			62				0.00
===================================================================

Our reduction layer definitely decreases the states explored, and thus the
memory used. It currently scales poorly with time however. We think a more
optimised version might definitely be of use for model checking, but due to
problems with the framework, we were not able to get there.

With the limited number of testing models used, we were unable to determine
whether RR or DF scheduling performs better.
