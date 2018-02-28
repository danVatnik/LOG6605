mtype = {msg1, msg2, msg3, alice, bob, intruder, 
 	numVerA, numVerB, numVerI,
	prefCryptA, prefCryptB, prefCryptI,
	sessKeyAB, sessKeyAI, sessKeyIB, 
	keyA, keyB, keyI,
	signA, signB, signI, 
	ok};

typedef msg1 { /* the encrypted part of a message */
  mtype sender, numVer, prefCrypt;
}

typedef msg2 { /* the encrypted part of a message */
  mtype numVer, perfCrypt, key;
}

typedef msg3 { /* the encrypted part of a message */
  mtype sessKey, key;
}

chan net1 = [0] of {mtype, /* msg# */
	mtype, /* receiver */
	ms1};

chan net2 = [0] of {mtype, /* msg# */
	mtype, /* receiver */
	ms2};

chan net3 = [0] of {mtype, /* msg# */
	mtype, /* receiver */
	ms3};

/* The partners successfully identified (if any) by initiator
   and responder, used in correctness assertion.
*/
mtype partnerA, partnerB;
mtype statusA, statusB;

/* Knowledge about nonces gained by the intruder. */
bool knowNA, knowNB;

active proctype Alice() {
	mtype partenerKey;
	msg1 data1;
	msg2 data2;
	msg3 data3;

	if /* nondeterministically choose a partner for this run */
  	:: partnerA = bob; partner_key = keyB;
  	:: partnerA = intruder; partner_key = keyI;
  fi;

	d_step{
		data1.sender = alice;
		data1.numVer = numVerA;
		data1.prefCrypt = prefCryptA;
	}

	net1 ! msg1(partnerA, data1);

	net2 ? msg2(alice, data2);	

	/* May need to set info in order to determine session key */
	end_errA:
		(data2.numVer == numVerB) && (data.prefCryp == perfCryptB)
	
	partenerKey = data2.key;

	/* May need to change in order to set session key */
	d_step{
		data3.sessKey = sessKeyAB;
		data3.key = partenerKey;
	}

	net3 ! msg3(partnerA, data);
	
  statusA = ok;
}

active proctype Bob(){

}
