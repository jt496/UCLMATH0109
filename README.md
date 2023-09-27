# Theorem Proving in Lean (MATH0109) 


This is the GitHub repository for the UCL Mathematics module Theorem Proving in Lean (MATH0109).

 All students should do the following before the end of Term 1

1) Get a free GitHub account at https://github.com/
 
2) Install everything (VS Code + Lean4 extension) by following steps 1-4 on this page
   https://lean-lang.org/lean4/doc/quickstart.html

3) Logout of your machine and then login again.

4) Clone the UCLMATH0109 repository by doing the following:

  a) Open VS Code
  
  b) Click on "Source Control"
  
  c) Click "Clone Repository"
  
  d) Click "Clone from GitHub"
    
(At this step VS Code may redirect you to login to GitHub so you can add it as a Trusted source.)

  e) The repository name is "jt496/UCL_MATH0109"

You will then need to choose a folder to store the code. You need to remember what this is!

A good choice might be "/my_home_directory/Lean4"


5) Once VS Code finishes downloading the code click on the "Terminal" menu and open a "New Terminal"

  Then in the terminal window that opens at the bottom of the screen type:

  lake clean

  lake exe cache get
  
  lake build UCLMATH0109
  
