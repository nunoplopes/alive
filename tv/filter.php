<?php

$dir = $argv[1];

foreach (glob("$dir/*.txt") as $f) {
  $f = file_get_contents($f);
  $f = preg_split('/^--------------------------*$/m', $f);
  array_shift($f);
  foreach ($f as $opt) {
    if (strpos($opt, 'Optimization is correct!')) continue;
    //if (strpos($opt, 'SMT solver gave up')) continue;
    //if (strpos($opt, 'out of memory')) continue;
    if (!preg_match('/(.*)=>(.*)/s', $opt, $a)) continue;
    //if (strpos($a[1], 'undef')) continue;
    //if (strpos($a[1], 'nsw')) continue;
    //if (strpos($a[1], 'nuw')) continue;
    //if (strpos($a[1], 'exact')) continue;
    if (strpos($a[1], ' select ')) continue;
    //if (strpos($a[2], ' sext ') || strpos($a[2], ' zext ')) continue;
    //if (strpos($opt, 'undefinedness')) continue;
    //if (strpos($opt, 'more poisonous')) continue;
    //if (strpos($opt, 'Mismatch in values')) continue;
    echo "\n----------------------------------------\n";
    echo trim($opt), "\n\n";
  }
}
