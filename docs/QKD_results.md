(I've deleted the html version of this file because git's rendering of this file is superior to an html browser's. So it's available at  

    https://github.com/mdxtoc/qtpi/blob/master/docs/QKD_results.md  
    
But if you are reading this then you already know that ...)

# Experiments with QKD

I've encoded QKD in qtpi, and played around with it. The simulation has taught me a lot. I thought for a while that I had found a (tiny) security hole, and then that I had made it a little bigger, then I thought that I probably hadn't, and then that I should try it out.

But actually it was all codswallop. My 'security hole' involved Eve somehow knowing the secret hash codes that Alice and Bob share initially. But such an Eve is just an intermediate agent in the way the protocol is supposed to work, conecting A to B by daisy-chaining A&harr;E, E&harr;F, ... Y&harr;Z; Z&harr;B. Obviously each of the intermediate agents has to be trusted; obviously if any is dishonest the whole chain is compromised. The research community is well aware of the problem, and well on top of it. So egg on my face. 

## The scenario

Alice has a message *M* which she wants to send to Bob. She has a quantum channel to him, and a [Wegman-Carter hash-tagged](#wegmancarter) two-way classical channel to him. She [calculates the number of qubits she will need](#enoughqubits), and sends them, one at a time and picking measurement basis and value for each at random, to Bob. Bob separately picks a random basis for each qubit, measures it in that basis, and records the results.

Then they do the QKD protocol dance: Alice sends the bases she chose to Bob through the classical channel and Bob sends the bases he chose back to Alice. They each select the subsequence of values for which they used the same basis, which will be about half of them, and throw the rest away. Now, supposing no interference with the qubits in transit, and no interference with the classical messages, they share the same sequence of code bits. Bob picks a subsequence of his code bits, sends a bit-mask to Alice to characterise it, and the subsequence itself. Alice looks at the corresponding subsequence of her own code bits: if they have the same code bits then the two subsequences should be identical. If the subsequences differ, and nothing is wrong with the classical communication, then something has interfered with Alice's quantum transmissions. If the subsequences are the same, then *probably* there's been no interference.

If all seems ok Alice deletes Bob's checkbits from her code bits, takes a prefix of what's left to exclusive-or mask the message *M*, and sends it down the classical channel to Bob. Bob, having deleted his checkbits from his own code bits, takes a prefix of the same length as Alice's communication, exclusive-or's the two, and he can see *M*. 

<a name="hashsecret"></a>
Before the protocol started Alice and Bob shared a secret: five 'short' one-time hash keys, one for each of the five classical messages they exchange (bases A&rarr;B, bases B&rarr;A, checkbit-mask B&rarr;A, checkbits B&rarr;A, encrypted message A&rarr;B). Each classical message is tagged by a hash of the message controlled by the corresponding hash key, and each tag is checked by the recipient, who uses the same hash function and knows the same hash key. If the tags aren't as expected then something is spoofing messages on the classical channel. If all is ok when the protocol is over, Alice and Bob each take five new hash keys from the unused suffix of their code bits, and they are ready to run the protocol again. Crucially, the classical messages are sent in the clear, but the secret code bits are never disclosed, apart from the checkbit sequence sent by Bob.

If there is an eavesdropper Eve, then the quantum and classical channels lead through her. She must do her best to read the quantum traffic between Alice and Bob, and to intercept and alter classical messages, and do it all without being noticed.

In the simulation we log the steps of the protocol, so our Alice, Bob and Eve each have a classical bit-list channel back to a logging process. In reality Alice and/or Bob would fall silent if they detected interference, but in the simulation we complete each trial even if something seems to be wrong. So Alice sends a blank (zero-length) message instead of an encrypted *M* if she detects classical or quantum-channel interference. 

In the real world Alice would make sure to pick enough qubits to ensure high probability that Bob can select enough check bits to reliably detect interference, and to give her enough code bits to encrypt *M* and refresh the hash keys. In the simulation she may be directed to pick too few. If so she doesn't pick new hash keys, and she sends only as much of *M* as she can encode. In practice not picking new hash keys would somewhat compromise the security of the classical channel, but this simulation doesn't try to exploit that.

In the past the exchange would be restarted if Alice found herself with too few code bits. But the way I did it messed up the analysis of the results, so it no longer happens. 

<a name="enoughqubits"></a>
## Picking enough qubits

(Simplified, 2021/11/18, to deal with a minimum number of checkbits.)

Suppose Alice's message *M* is *m* bits long and the management have decided to use *c* checkbits and *w*-bit keys for the Wegman-Carter authentication. We know that there are five classical messages per trial, so she needs at least

&emsp;&emsp;*k* = *m*+*c*+5*w*

secret code bits: *m* to encrypt *M* and send it to Bob, *c* for checkbits, 5*w* to use for new hash keys. if *N* is the number of qubits she sends, then she can expect that about *N*/2 code bits will be agreed with Bob.

She must allow for statistical variation: sometimes she and Bob will agree fewer, sometimes more, code bits. She knows that the standard deviation &sigma; of the number of successes when choosing with probability *p* from a sequence length *n* is &radic;<span style="text-decoration:overline;">&nbsp;*np*(1-*p*)&nbsp;</span>. She wants the probability of choosing too few bits to be very small, so she must over-estimate. If she wants to be *s* &sigma;s away from trouble, well into the tail of the normal distribution, she can write some equations. 

Alice and Bob will agree on the measurement basis for a qubit with probability 1/2. So she can calculate 

&emsp;&emsp;*N*/2 &ge; *k* + *s*&radic;<span style="text-decoration:overline;">&nbsp;*N*(1/2)(1/2)&nbsp;</span>

&emsp;&emsp;&emsp;&ensp;= *k* + *s*/2&radic;<span style="text-decoration:overline;">&nbsp;*N*&nbsp;</span>

Taking the inequality as an equality, this is a quadratic in &radic;<span style="text-decoration:overline;">&nbsp;*N*&nbsp;</span>:

&emsp;&emsp;*N*/2 - *s*/2&radic;<span style="text-decoration:overline;">&nbsp;*N*&nbsp;</span> - *k* = 0

One of the solutions of this equation is negative, so we ignore it and take the positive solution: qtpi's *num* type includes both integers and unbounded-precision rationals, so she can calculate the root directly. (Of course we still use an approximation for *sqrt*.) 

The calculation so far isn't quite right, because Bob chooses checkbits at random from the *N*/2 that he and Alice share. If he chose with probability 2*c*/*N* he would get *c* checkbits *on average*. He wants the minimum -- i.e. the number which is *s*&sigma; away from the mean -- to be *c*. He has to shoot a little higher. A better guess would be 

&emsp;&emsp;*cmin* = *c*+*s*&radic;<span style="text-decoration:overline;">&nbsp;*c*&nbsp;</span>

-- possibly overkill, but safety first. But then we have to worry about Bob taking too many checkbits, and not leaving enough for Alice. So we ought to allow another *s*&radic;<span style="text-decoration:overline;">&nbsp;*c*&nbsp;</span> for that. At any rate, plug *cmin*+*s*&radic;<span style="text-decoration:overline;">&nbsp;*c*&nbsp;</span> in place of *c* in the quadratic above and we're likely to get the right number of checkbits.

The [no Eve trials](#noEve) show how many bits Alice uses for various values of *m*, *s*, *c* and *w*, and how it affects the repetition rate.

<a name="wegmancarter"></a>
## Wegman-Carter hash-tagging

For verisimilitude I implement hash tagging. But it doesn't make a difference: in the simulation Eve can either hack it perfectly ([clever Eve](#cleverEve)) or she doesn't even try ([naive Eve](#naiveEve)).

Wegman-Carter tagging seems too computationally expensive whilst qtpi is a naively interpreted language. So I do something simpler, because I'm not simulating security against code-crackers. It's still a hash, and experiment shows that if Eve accidentally gets her keys muddled up, Alice and Bob notice.

For a hash-key size *w* choose packet size *p* = *w*/3\*4+1. Divide the bit sequence to be hashed into packets size 2*p*; convert each packet to an integer; multiply by the hash key; mask with 2<sup>*p*</sup>-1 to reduce the size of the result; convert back to bit strings and concatenate. That will have reduced the size of the bit-string by half. Repeat until you have no more than *p* bits, and that's the tag. 

<a name="noEve"></a>
## No Eve: just Alice and Bob

Trials to see if Alice picks enough qubits. Interference never detected because there isn't any: command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                    SystemAB.qtp)

### Hash tags

  * The hash calculations are implemented in the qtpi functional language and therefore slowly interpreted. But it works: Bob and Alice each agree that the other isn't spoofing classical messages.
  
        length of message? 1000
        minimum number of checkbits? 100
        length of a hash key? 40
        number of sigmas? 5
        number of trials? 1000

        3078 qubits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 0 short codebits; 
            average check bits 150.01 minimum check bits 106
        histogram of check-bit lengths 
        [(106,1);(112,1);(116,1);(118,1);(121,4);(122,3);(123,3);(124,2);(125,4);(126,5)
        ;(127,8);(128,8);(129,7);(130,7);(131,8);(132,16);(133,16);(134,17);(135,10);(
        136,18);(137,14);(138,21);(139,19);(140,18);(141,22);(142,22);(143,26);(144,26);
        (145,25);(146,42);(147,26);(148,39);(149,33);(150,26);(151,37);(152,37);(153,34)
        ;(154,39);(155,26);(156,26);(157,38);(158,28);(159,27);(160,22);(161,21);(162,21
        );(163,16);(164,20);(165,17);(166,14);(167,14);(168,9);(169,13);(170,6);(171,1);
        (172,5);(173,4);(174,8);(175,3);(176,4);(177,3);(178,3);(179,1);(184,1);(185,1);
        (186,1);(190,1)]

        15.10s user 0.04s system

  * (Quite a lot faster than it used to be: 3M qubits in 15 seconds.) 
  * It is now only about 25% faster with hash tagging turned off (which is what 0-length hash keys do).

        length of message? 1000
        minimum number of checkbits? 100
        length of a hash key? 0
        number of sigmas? 5
        number of trials? 1000

        2658 qubits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 0 short codebits; 
            average check bits 150.51 minimum check bits 112
        histogram of check-bit lengths 
        [(112,1);(118,1);(119,1);(120,1);(121,1);(122,3);(123,1);(124,3);(125,5);(126,6)
        ;(127,5);(128,4);(129,7);(130,12);(131,2);(132,4);(133,8);(134,9);(135,10);(136,
        15);(137,19);(138,21);(139,26);(140,31);(141,26);(142,24);(143,21);(144,31);(145
        ,34);(146,30);(147,44);(148,33);(149,34);(150,35);(151,41);(152,29);(153,39);(
        154,30);(155,28);(156,32);(157,31);(158,20);(159,30);(160,25);(161,18);(162,15);
        (163,21);(164,14);(165,12);(166,11);(167,11);(168,18);(169,12);(170,4);(171,13);
        (172,6);(173,3);(174,8);(175,3);(176,2);(177,5);(178,5);(179,3);(180,1);(181,1);
        (183,1)]


        11.86s user 0.03s system
  
### 0 Sigma  
* Checking the minimum qubits calculation. It works, but note that with 0&sigma; Alice runs out of bits as many times as not, and about half the time Bob uses fewer than the minimum number of checkbits.

        length of message? 1000
        minimum number of checkbits? 100
        length of a hash key? 40
        number of sigmas? 0
        number of trials? 1000

        2601 qubits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 1010 short codebits; 
            average check bits 97.36 minimum check bits 71
        histogram of check-bit lengths 
        [(71,2);(72,1);(74,1);(75,2);(76,1);(77,4);(78,9);(79,2);(80,12);(81,10);(82,10)
        ;(83,10);(84,17);(85,12);(86,14);(87,17);(88,38);(89,28);(90,32);(91,23);(92,44)
        ;(93,50);(94,41);(95,47);(96,48);(97,49);(98,42);(99,36);(100,43);(101,31);(102,
        31);(103,38);(104,39);(105,31);(106,26);(107,34);(108,20);(109,16);(110,16);(111
        ,15);(112,10);(113,9);(114,12);(115,3);(116,6);(117,5);(118,2);(119,4);(121,3);(
        123,1);(127,1);(128,1);(135,1)]

        24.68s user 0.05s system 99% cpu 24.770 total

        
### 1 Sigma

  * A longer message but 1 &sigma;. The short-message rate is about 12%. Bob is below the minimum number of checkbits about 14% of the time.
  
        length of message? 1000
        minimum number of checkbits? 100
        length of a hash key? 40
        number of sigmas? 1
        number of trials? 1000

        2692 qubits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 116 short codebits; average check bits 109.34 minimum check bits 82
        histogram of check-bit lengths 
        [(82,1);(83,2);(84,1);(86,1);(87,2);(89,5);(90,5);(91,6);(92,8);(93,11);(94,11);(
        95,19);(96,15);(97,16);(98,16);(99,28);(100,29);(101,40);(102,35);(103,26);(104,
        34);(105,43);(106,47);(107,35);(108,42);(109,45);(110,50);(111,41);(112,25);(113
        ,49);(114,20);(115,35);(116,38);(117,30);(118,19);(119,21);(120,22);(121,14);(
        122,12);(123,19);(124,13);(125,19);(126,6);(127,6);(128,5);(129,11);(130,5);(131
        ,7);(132,4);(133,1);(136,2);(137,2);(143,1)]

        14.66s user 0.03s system
  
### More Sigma

* With 3&sigma; we see no short messages, but Bob sometimes undercooks the checkbits. With 5&sigma; he never does.

        length of message? 1000
        minimum number of checkbits? 100
        length of a hash key? 40
        number of sigmas? 3
        number of trials? 1000

        2882 qubits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 0 short codebits; 
            average check bits 130.38 minimum check bits 92
        histogram of check-bit lengths 
        [(92,1);(100,1);(101,1);(103,1);(104,3);(106,1);(107,5);(108,3);(109,3);(110,16)
        ;(111,12);(112,10);(113,16);(114,7);(115,8);(116,15);(117,19);(118,13);(119,19);
        (120,25);(121,29);(122,29);(123,31);(124,36);(125,25);(126,35);(127,37);(128,27)
        ;(129,33);(130,40);(131,40);(132,38);(133,41);(134,27);(135,31);(136,18);(137,32
        );(138,37);(139,30);(140,33);(141,26);(142,25);(143,18);(144,15);(145,19);(146,9
        );(147,11);(148,7);(149,6);(150,7);(151,2);(152,1);(153,5);(154,2);(155,4);(156,
        1);(157,2);(158,3);(159,2);(160,2);(163,2);(165,1);(166,1);(171,1)]

        14.13s user 0.04s system
        
        ...
        length of message? 1000
        minimum number of checkbits? 100
        length of a hash key? 40
        number of sigmas? 5
        number of trials? 1000

        3078 qubits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 0 short codebits; 
                average check bits 150.24 minimum check bits 117
        histogram of check-bit lengths 
        [(117,1);(118,1);(120,1);(121,1);(122,4);(123,2);(124,3);(125,5);(126,4);(127,3)
        ;(128,2);(129,7);(130,6);(131,13);(132,13);(133,8);(134,12);(135,12);(136,24);(
        137,31);(138,27);(139,21);(140,28);(141,14);(142,22);(143,23);(144,32);(145,41);
        (146,25);(147,26);(148,26);(149,27);(150,31);(151,27);(152,32);(153,33);(154,42)
        ;(155,33);(156,38);(157,30);(158,23);(159,22);(160,30);(161,27);(162,13);(163,27
        );(164,14);(165,13);(166,21);(167,10);(168,10);(169,10);(170,8);(171,5);(172,9);
        (173,6);(174,7);(175,2);(176,2);(177,3);(178,1);(179,1);(180,1);(181,2);(184,1);
        (185,1)]

        15.39s user 0.05s system

<a name="naiveEve"></a>
## Alice, Bob and naive Eve

This is the intervention everybody knows about -- intercept and resend. The quantum and classical channels that are connected to Alice in fact go to [Eve](#whyEve), who also has quantum and classical channels connected to Bob. So she can potentially intervene on either of them, or just pass on messages from one to the other.

Eve knows the protocol, and she knows Alice's and Bob's implementation (but they don't know hers). Like Alice and Bob she knows *N* (I used to program it differently: now I think it's more realistic if the packet size is part of the definition of the system). 

If she passes on the qubits she sees without measuring them, and passes on classical messages likewise, she is undetectable, like a network node. If she measures the qubits before sending them, she will be detected with a probability of 1-(3/4)<sup>c</sup> where *c* is the number of checkbits Bob generates. If she tries to send messages on the classical channel, guessing the hash keys, she will be detected with a probability of 1-(1/2)<sup>5*w*</sup>. 

My simulation of naive Eve does indeed measure and re-transmit the qubits she receives. She is, as a consequence, pretty much always detected. Once she's spotted, Alice doesn't encrypt and send *M*, so even if Eve could hack the classical channel it wouldn't do her much good. In my simulation naive Eve simply re-transmits classical messages.

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                    naiveEve.qtp LogEve.qtp SystemAEB.qtp)

Note that the simulation runs the exact same Alice, Bob and their loggers as the Eve-free simulation did. The SystemAEB file runs Alice, Bob and naive Eve in parallel with their three loggers.

* If Alice goes for super-safety in the number of qubits she uses, then she detects interference _every_ time in the short simulations I have time to run. Her chance of evading detection with 119 checkbits -- the minimum number Bob in this example -- is about 10<sup>-15</sup>.
  
        length of message? 1000
        minimum number of checkbits? 100
        length of a hash key? 40
        number of sigmas? 5
        number of trials? 1000

        3078 qubits per trial
        all done: 0 Eve's; 1000 Alice's; 0 successful evasions; 0 short codebits; 
            average check bits (Alice/Eve) 150.25; minimum check bits (Alice/Eve) 119; 
            average check bits (Eve/Bob) 150.25; minimum check bits (Eve/Bob) 119

        25.96s user 0.08s system 

 * If Alice sends short messages and doesn't care about statistical variation, Eve can occasionally win. (It's safe, in this simulation, to use zero-length hash tags so as to increase the effect of statistical variation, because Eve isn't programmed to interfere with the classical channel.)  
* The number of evasions -- trials where Eve goes undetected -- is as predicted by analysis, where Eve has 75% chance of evading detection on each checkbit. But note that Eve wins, in the sense of reading the message correctly and transmitting it on to Bob, far more rarely. The settings are deliberately ridiculous, to provoke that kind of result.  

        length of message? 10
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        26 qubits per trial
        all done: 35 Eve's; 483 Alice's; 517 successful evasions; 667 short codebits; 
            average check bits (Alice/Eve) 2.42; minimum check bits (Alice/Eve) 0; 
                average check bits (Eve/Bob) 2.42; minimum check bits (Eve/Bob) 0
        histogram of check-bit lengths (Alice/Eve) [(0,63);(1,183);(2,296);(3,271);(4,122);(5,52);(6,12);(7,1)]
        histogram of check-bit lengths (Eve/Bob) [(0,63);(1,183);(2,296);(3,271);(4,122);(5,52);(6,12);(7,1)]
        histogram of evasions [(0,63);(1,135);(2,169);(3,110);(4,29);(5,9);(6,2);(7,0)]

        0.47s user 0.01s system

## A clever Eve

If Eve knows the hash codes used on the classical channel then she can pretend to be Bob to Alice and Alice to Bob. In effect she becomes an intermediate node, and it's important to stress that *that's the way the protocol is supposed to work*, with intermediate trusted nodes playing Bob to one segment and Alice to the next, decrypting and re-encrypting each message as it passes, using distinct one-time codes on each segment.

* It doesn't reveal anything about the protocol, but here are the results anyway: naturally, it takes about twice as long to simulate as a simple Alice to Bob setup (a bit more because it prints out more on each trial).

        length of message? 1000
        minimum number of checkbits? 100
        length of a hash key? 40
        number of sigmas? 5
        number of trials? 1000

        3078 qubits per trial
        all done: 1000 Eve's; 0 Alice's; 1000 successful evasions; 0 short codebits; 
            average check bits (Alice/Eve) 150.14; minimum check bits (Alice/Eve) 110; 
            average check bits (Eve/Bob) 149.75; minimum check bits (Eve/Bob) 119

        28.79s user 0.08s system

<a name="whyEve"></a>
## Why "Eve"?

"Eve" from "eavesdropper"? I do hope so. Not, I hope, from any notion of females as deceptive.
