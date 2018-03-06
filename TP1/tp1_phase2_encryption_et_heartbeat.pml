mtype = {msg1, msg2, msg3, msg4, msg5, 
    alice, bob, intruder, 
 	numVerA, numVerB, numVerI,
	prefCryptA, prefCryptB, prefCryptI,
	sessKeyAB, sessKeyAI, sessKeyIB,
    pubKeyA, pubKeyB, privKeyB, pubKeyI,
	keyA, keyB, keyI,
	signA, signB, signI, 
    valA, valI,
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

typedef m4 { /* the encrypted part of a message */
  mtype sender, length, val;
}

typedef m5 { /* the encrypted part of a message */
  mtype val, extraVal, sessKey;
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

chan net4 = [0] of {mtype, /* msg# */
	mtype, /* receiver */
	m4};

chan net5 = [0] of {mtype, /* msg# */
	mtype, /* receiver */
	m5};

bool sessKeyValid = true;
bool gotSessKey = false;
bool connectedA = false;

mtype partnerA, partnerA2, partnerB, partnerI, partnerI2;
mtype statusA, statusB, statusI;


active proctype Alice() {
    mtype partnerKey, sessionKey;

    m1 data1;
	m2 data2;
	m3 data3;
    m4 data4;
    m5 data5;

  	partnerA = bob;

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
    :: (partnerA2 == bob) -> sessionKey = sessKeyAB;
    :: else -> skip;
	fi;

    d_step{
		data3.sessKey = sessionKey;
		data3.key = partnerKey;
	}

	net3 ! msg3(partnerA2, data3);
    
    connectedA = true;
    
    do
    :: data4.sender = alice;
		data4.length = true;
		data4.val = valA;

        net4 ! msg4(partnerA, data4);

        net5 ? msg5(alice, data5);

    od;
}

active proctype Bob() {
    m1 data1;
	m2 data2;
	m3 data3;
    m4 data4;
    m5 data5;

    do
    :: net1 ? msg1(bob, data1) -> 
        d_step{
            partnerB = data1.sender;

            data2.numVer = numVerB;
            data2.prefCrypt = prefCryptB;
            data2.sender = bob;
            data2.key = keyB;
        
        }
        net2 ! msg2(partnerB, data2);
    :: net3 ? msg3(bob, data3) -> 
        end_errB: 
        (data3.key == keyB);
    :: net4 ? msg4(bob, data4) ->
            partnerB = data4.sender;

            data5.val = data4.val;

            if
            :: (partnerB == alice) -> data5.sessKey = sessKeyAB;
            :: (partnerB == intruder) -> data5.sessKey = sessKeyIB;
            fi;

            if
            :: (data4.length == false) -> 
                if
                :: data5.extraVal = numVerB;
                :: data5.extraVal = prefCryptB;
                :: data5.extraVal = pubKeyB;
                :: data5.extraVal = privKeyB;
                :: data5.extraVal = signB;
                :: data5.extraVal = numVerA;
                :: data5.extraVal = prefCryptA;
                :: data5.extraVal = pubKeyA;
                :: (connectedA) -> data5.extraVal = sessKeyAB;
                :: data5.extraVal = numVerI;
                :: data5.extraVal = prefCryptI;
                :: data5.extraVal = pubKeyI;
                :: data5.extraVal = sessKeyIB;
                fi;
            :: else -> skip;
            fi;

        net5 ! msg5(partnerB, data5);
    od;
}

active proctype Intruder() {
    mtype partnerKey, sessionKey;
    m1 data1;
	m2 data2;
	m3 data3;
    m4 data4;
    m5 data5;

  	partnerI = bob;

	d_step{
		data1.sender = intruder;
		data1.numVer = numVerI;
		data1.prefCrypt = prefCryptI;
	}

    net1 ! msg1(partnerI, data1);

	net2 ? msg2(intruder, data2);	
	
	partnerKey = data2.key;

    partnerI2 = data2.sender;

    if
    :: (partnerI2 == bob) -> sessionKey = sessKeyIB;
    :: else -> skip;
	fi;

    d_step{
		data3.sessKey = sessionKey;
		data3.key = partnerKey;
	}

	net3 ! msg3(partnerI2, data3);

    do
    ::  data4.sender = intruder;
		data4.length = false;
		data4.val = valI;


        net4 ! msg4(partnerI, data4);

        net5 ? msg5(intruder, data5);

        if
        :: (data5.extraVal == sessKeyAB ) -> gotSessKey = true;
        :: else -> gotSessKey = false;
        fi;
    od;
}

ltl p1 {[]!gotSessKey}