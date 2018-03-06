mtype = {msg1, msg2, alice, bob, intruder, 
 	valA, valI,
    numVerA, numVerB, numVerI,
	prefCryptA, prefCryptB, prefCryptI,
	sessKeyAB, sessKeyAI, sessKeyIB, 
	pubKeyA, pubKeyB, privKeyB, pubKeyI,
	signA, signB, signI, 
	ok,
    };

typedef m1 { /* the encrypted part of a message */
  mtype sender, length, val;
}

typedef m2 { /* the encrypted part of a message */
  mtype val, extraVal, sessKey;
}

chan net1 = [0] of {mtype, /* msg# */
	mtype, /* receiver */
	m1};

chan net2 = [0] of {mtype, /* msg# */
	mtype, /* receiver */
	m2};

bool gotExtraVal = false;
bool sessKeyValid = true;

mtype partnerA, partnerB, partnerI;
mtype statusA, statusB, statusI;

active proctype Alice() {
    m1 data1;
	m2 data2;
    mtype sessKey;

  	partnerA = bob; 
    sessKey = sessKeyAB;

	d_step{
		data1.sender = alice;
		data1.length = true;
		data1.val = valA;
	}

	net1 ! msg1(partnerA, data1);

    net2 ? msg2(alice, data2);

    end_errA:
        (data2.sessKey == sessKey) && (data2.val == valI);

    if
    :: (data2.sessKey == sessKey) -> sessKeyValid = true;
    :: else -> sessKeyValid = false;
    fi;

    statusA = ok;
}

active proctype Bob() {
    m1 data1;
	m2 data2;

    net1 ? msg1(bob, data1);

    partnerB = data1.sender;

    data2.val = data1.val;

    if
    :: (partnerB == alice) -> data2.sessKey = sessKeyAB;
    :: (partnerB == intruder) -> data2.sessKey = sessKeyIB;
    fi;

    if
    :: (data1.length == false) -> 
        if
        :: data2.extraVal = numVerB;
        :: data2.extraVal = prefCryptB;
        :: data2.extraVal = pubKeyB;
        :: data2.extraVal = privKeyB;
        :: data2.extraVal = signB;
        :: data2.extraVal = numVerA;
        :: data2.extraVal = prefCryptA;
        :: data2.extraVal = pubKeyA;
        :: data2.extraVal = sessKeyAB;
        :: data2.extraVal = numVerI;
        :: data2.extraVal = prefCryptI;
        :: data2.extraVal = pubKeyI;
        :: data2.extraVal = sessKeyIB;
        fi;
    :: else -> skip;
    fi;

    net2 ! msg2(partnerB, data2);

    statusB = ok;
}

active proctype Intruder() {
    m1 data1;
	m2 data2;
    mtype sessKey, length;

  	partnerI = bob; 
    sessKey = sessKeyIB;


    if
    :: length = true;
    :: length = false;
    fi;
    
    d_step {
        data1.sender = intruder;
        data1.length = length;
        data1.val = valI;
    }

	net1 ! msg1(partnerI, data1);

    net2 ? msg2(intruder, data2);

    end_errI:
        (data2.sessKey == sessKey) && (data2.val == valI);
    
    if
    :: (data2.extraVal != 0 ) -> gotExtraVal = true;
    :: else -> gotExtraVal = false;
    fi;

    if
    :: (data2.sessKey == sessKey) -> sessKeyValid = true;
    :: else -> sessKeyValid = false;
    fi;

    statusI = ok;
}

ltl p1{ [](partnerA == bob -> sessKeyValid)}