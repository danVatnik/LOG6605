mtype = {msg1, msg2, msg3, alice, bob, intruder, 
 	numVerA, numVerB, numVerI,
	prefCryptA, prefCryptB, prefCryptI,
	sessKeyAB, sessKeyAI, sessKeyIB, 
	keyA, keyB, keyI,
	signA, signB, signI, 
	ok};

typedef m1 { /* the encrypted part of a message */
  mtype sender, numVer, prefCrypt;
}

typedef m2 { /* the encrypted part of a message */
  mtype numVer, prefCrypt, key;
}

typedef m3 { /* the encrypted part of a message */
  mtype sessKey, key;
}

chan net1 = [0] of {mtype, /* msg# */
	mtype, /* receiver */
	m1};

chan net2 = [0] of {mtype, /* msg# */
	mtype, /* receiver */
	m2};

chan net3 = [0] of {mtype, /* msg# */
	mtype, /* receiver */
	m3};

/* The partners successfully identified (if any) by initiator
   and responder, used in correctness assertion.
*/
mtype partnerA, partnerB;
mtype statusA, statusB;

/* Knowledge about nonces gained by the intruder. */
bool knowNA, knowNB;

active proctype Alice() {
	mtype partnerKey;
	m1 data1;
	m2 data2;
	m3 data3;

	if /* nondeterministically choose a partner for this run */
  	:: partnerA = bob; partnerKey = keyB;
  	:: partnerA = intruder; partnerKey = keyI;
  fi;

	d_step{
		data1.sender = alice;
		data1.numVer = numVerA;
		data1.prefCrypt = prefCryptA;
	}

	net1 ! msg1(partnerA, data1);

	net2 ? msg2(alice, data2);	

	/* CHeck if key form B or I */
	end_errA:
		(data2.numVer == numVerB) && (data2.prefCrypt == prefCryptB)
	
	partnerKey = data2.key;

	/* Choose proper session key */

	/* May need to change in order to set session key */
	d_step{
		data3.sessKey = sessKeyAB;
		data3.key = partnerKey;
	}

	net3 ! msg3(partnerA, data3);

  statusA = ok;
}

active proctype Bob(){
	m1 data1;
	m2 data2;
	m3 data3;

	net1 ? msg1(bob, data1);

  partnerB = data1.sender;

	d_step {
    data2.numVer = numVerB;
    data2.prefCrypt = prefCryptB;
    data2.key = keyB;
  }

  net2 ! msg2(partnerB, data2);

	net3 ? msg3(bob, data3);

	/* Some kind of error is possible not sure if needed */
	end_errB2: 
  	(data3.key == keyB);

  statusB = ok;
}

active proctype Intruder(){

	/* peut initier, intercepter, renvoyer (modifier ce qu'il peut) */
	/* know session id */

}
