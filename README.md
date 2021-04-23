# acl2s-merge-insert-ordered-assoc
Andrew Briasco-Stewart\
briasco-stewart.a@northeastern.edu\
Christopher Swagler\
swagler.c@northeastern.edu\
Steve Liu\
liu.steve@northeastern.edu

Final project for CS 2800. Formally proving the associativity of a merge-ordered-insert function in ACL2s.

This repo contains all of the work compiled from proving the associativity of a merge-ordered-insert and goes alongside the paper on the proof. The main file for this repo is official_proof.lisp and contains all of the functions required for the main theorem alongside its necessary lemmas. walkthrough_proof.lisp gives a more detailed explanation of the steps and work from official_proof.lisp. The other two files, proposal.lisp and project_work.lisp contain our testing and highlights all of the trials and tribulations required to get ACL2 to accept the main theorem.


In order to run the code for our proof:
1. Download the official_proof.lisp from this repository.
2. Launch your favorite ACL2 processing language. We recommend using [Eclipse](https://www.google.com), and the following directions assume Eclipse is the environment you are in.
3. Create a new project folder within your workspace and drop file into that folder.
4. Right click on the project folder and hit refresh.
5. Start a new session of ACL2 (the green play button) and hit the icon that extends the ACL2 to-do line all the way down to the end of the file (two arrows pointing down).
6. ACL2 will ask you to create an association .a2s file, hit yes.
7. Let the proof run for a bit (about a minute or two).
 
