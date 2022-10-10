for file in $(ls *.cmt) 
  do
  reanalyze-test -debug -exception-cmt $file 2>&1 | cat >debug.$file.log
  done
