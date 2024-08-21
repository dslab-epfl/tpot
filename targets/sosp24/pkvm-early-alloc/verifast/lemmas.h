/*PROOF*/ /*@ lemma_auto void characters_zeroed_join(char *array);
/*PROOF*/     requires [?f]characters_zeroed(array, ?n) &*& [f]characters_zeroed(array + n, ?n0);
/*PROOF*/     ensures [f]characters_zeroed(array, n + n0); @*/
