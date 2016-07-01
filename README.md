# bhcspprover
The provers of bHCSP and a train on-board control example .
All of them are implemented in Isabelle2015. 

The embedding of the prover based on the time aware inference system includes the following files:
ILSequent.thy,
DCSequent.thy, 
bHCSP_Com.thy,
Inference.thy

And the train on-board control example is modelled in Train.thy, and verified in TrainProof.thy.

The embedding of the prover based on the time oblivious inference system includes the following files:
bSyntax_SL.thy,
Inferenc_SL.thy

And the train on-board control example is modelled in Train_SL.thy, and verified in TrainProof_SL.thy.

