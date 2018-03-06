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
  mtype numVer, prefCrypt, sender, key;
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
mtype partnerA, partnerA2, partnerB;
mtype statusA, statusB;

/* Knowledge about nonces gained by the intruder. */
bool knowSessKey;
bool secretSender = true;

active proctype Alice() {
	mtype partnerKey, sessionKey, intruderDetected;
	m1 data1;
	m2 data2;
	m3 data3;

	if /* nondeterministically choose a partner for this run */
  	:: partnerA = bob;
  	:: partnerA = intruder;
  	fi;

	d_step{
		data1.sender = alice;
		data1.numVer = numVerA;
		data1.prefCrypt = prefCryptA;
	}

	net1 ! msg1(partnerA, data1);

	net2 ? msg2(alice, data2);	
	
	partnerKey = data2.key;

    partnerA2 = data2.sender;

    if
    :: partnerA != partnerA2 -> intruderDetected = true;
    :: else -> intruderDetected = false;
    fi;

	/* Choose proper session key */
	if
		:: (partnerA2 == bob) -> sessionKey = sessKeyAB;
		:: (partnerA2 == intruder) -> sessionKey = sessKeyAI;
	fi;

	d_step{
		data3.sessKey = sessionKey;
		data3.key = partnerKey;
	}

	net3 ! msg3(partnerA2, data3);

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
    data2.sender = bob;
    data2.key = keyB;
  }

  net2 ! msg2(partnerB, data2);

	net3 ? msg3(bob, data3);

	end_errB: 
  	(data3.key == keyB);

	if
	:: (partnerB == alice && data3.sessKey == sessKeyAB) -> secretSender = true;
	:: (partnerB == intruder && data3.sessKey == sessKeyIB) -> secretSender = true;
	:: else -> secretSender = false;
	fi;

  statusB = ok;
}

active proctype Intruder(){

	mtype msg, msg_type;
	m1 data1, intercepted1;
	m2 data2, intercepted2;
	m3 data3, intercepted3;
	/* peut initier, intercepter, renvoyer (modifier ce qu'il peut) */
	/* know session id */

	do
	::
		if
		:: msg_type == msg1 -> 
			if
			:: data1.sender = alice;
			:: data1.sender = intruder;
			fi;
			if
			:: data1.numVer = intercepted1.numVer; data1.prefCrypt = intercepted1.prefCrypt;
			:: data1.numVer = numVerI; data1.prefCrypt = prefCryptI;
			fi;
			net1 ! msg1(bob, data1);
		fi;
	::
		if
		:: msg_type == msg2 -> 
			data2.key = intercepted2.key;
            data2.sender = intercepted2.sender;
			if
			:: data2.numVer = intercepted2.numVer; data2.prefCrypt = intercepted2.prefCrypt;
			:: data2.numVer = numVerI; data2.prefCrypt = prefCryptI;
			fi;
			net2 ! msg2(alice, data2);
		fi;
	::
		if
		:: msg_type == msg3 -> 
			if
			:: (knowSessKey) -> data3.sessKey = intercepted3.sessKey; data3.key = keyB;
			:: else -> skip;
			fi;
			net3 ! msg3(bob, data3);
		fi;
	::
		net1 ? msg1(intruder, data1) ->
		if
		:: d_step{
				intercepted1.sender = data1.sender;
				intercepted1.numVer = data1.numVer;
				intercepted1.prefCrypt = data1.prefCrypt;
				msg_type = msg1;
			}
		:: skip;
		fi;
	::
		net2 ? msg2(intruder, data2) ->
		if
		:: d_step{
				intercepted2.numVer = data2.numVer;
				intercepted2.prefCrypt = data2.prefCrypt;
				intercepted2.key = data2.key;
                intercepted2.sender = data2.sender;
				msg_type = msg2;
			}
		:: skip;
		fi;
	::
		net3 ? msg3(intruder, data3) ->
		if
		:: d_step{
				if
				:: (data3.key == keyI) -> knowSessKey = true;
				fi;
				intercepted3.sessKey = data3.sessKey;
				intercepted3.key = data3.key;
				msg_type = msg3;
			}
		:: skip;
		fi;

	od;
}

ltl p1 {[]secretSender}