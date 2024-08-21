/*GLOBAL*/ predicate void Byte (pointer p) {
/*GLOBAL*/   take B = Owned<char>(p);
/*SYNTAX*/ /*GLOBAL*/   return;
/*SYNTAX*/ /*GLOBAL*/ }

/*GLOBAL*/ predicate void ByteV (pointer p, integer the_value) {
/*GLOBAL*/   take B = Owned<char>(p);
/*GLOBAL*/   assert (B == the_value);
/*SYNTAX*/ /*GLOBAL*/   return;
/*SYNTAX*/ /*GLOBAL*/ }


/*GLOBAL*/ predicate void EarlyAlloc (pointer cur, integer end) {
/*GLOBAL*/   assert ((0 <= ((integer) cur)) && (((integer) cur) <= end));
/*GLOBAL*/   take R = 
/*GLOBAL*/     each(integer q; ((integer) cur) <= q && q <= (end - 1)) { 
/*GLOBAL*/       Byte((pointer)(((integer)((pointer) 0)) + (q*1))) 
/*SYNTAX*/ /*GLOBAL*/   };
/*SYNTAX*/ /*GLOBAL*/   return;
/*SYNTAX*/ /*GLOBAL*/ }
