# Experiments with QKD

I've encoded QKD in qtpi, and played around with it. The simulation has taught me a lot. I thought for a while that [I had found a (tiny) security hole](#cleverEve), and then that [I had made it a little bigger](#superEve), but I now realise that [I probably hadn't](#notreally).

## The scenario

Alice has a message *M* which she wants to send to Bob. She has a quantum channel to him (at least she *thinks* it goes to him), and a [Wegman-Carter hash-tagged](#wegmancarter) two-way classical channel to him. She [calculates the number of qbits she will need](#enoughqbits), and sends them, one at a time and picking measurement basis and value for each at random, to Bob. Bob separately picks a random basis for each qbit, measures it in that basis, and records the results.

Then they do the QKD protocol dance: Alice sends the bases she chose to Bob through the classical channel and Bob sends the bases he chose back to Alice. They each select the subsequence of values for which they used the same basis, which will be about half of them, and throw the rest away. Now, supposing no interference with the qbits in transit, and no interference with the classical messages, they share the same sequence of code bits. Bob picks a subsequence of his code bits, sends a bit-mask to Alice to characterise it, and the subsequence itself. Alice looks at the corresponding subsequence of her own code bits: if they have the same code bits then the two subsequences should be identical, with probability 1-1/2<sup>*c*</sup>, where *c* is the number of bits Bob picks. If the subsequences differ, and nothing is wrong with the classical communication, then something has interfered with Alice's quantum transmissions.

If all seems ok Alice deletes Bob's checkbits from her code bits, takes a prefix of them to exclusive-or mask the message *M*, and sends it down the classical channel to Bob. Bob, having deleted his checkbits from his own code bits, takes a prefix of the same length, exclusive-or's it with the encrypted message, and he can see *M*. 

<a name="hashsecret"></a>
Before the protocol started Alice and Bob shared a secret: five short one-time hash keys, one for each of the five classical messages they exchange (bases A&rarr;B, bases B&rarr;A, bit-mask B&rarr;A, subsequence B&rarr;A, encrypted message A&rarr;B). Each classical message is tagged by a hash of the message and the corresponding hash key, and each tag is checked by the recipient, who uses the same hash function and knows the same hash key. If the tags aren't as expected then something is spoofing messages on the classical channel. If all is ok when the protocol is over, Alice and Bob each take five new hash keys from the unused suffix of their code bits, and they are ready to run the protocol again. Crucially, the messages are sent in the clear, but the secret code bits are never disclosed, apart from the checkbit sequence sent by Bob.

If there is an eavesdropper Eve, then the quantum and classical channels lead through her. She must do her best to read the quantum traffic between Alice and Bob, and to intercept and alter classical messages, and do it all without being noticed.

In the simulation we log the steps of the protocol, so our Alice, Bob and Eve each have a classical bit-list channel back to a logging process. In reality Alice and/or Bob would fall silent if they detected interference, but in the simulation we complete each trial even if something seems to be wrong. So Alice sends a blank message instead of an encrypted *M* if she detects quantum-channel interference, and each of them keeps going even if they detect classical-channel interference. In reality Alice would be sure to pick enough qbits to ensure near certainty that Bob can select enough check bits to reliably detect interference, and to give her enough code bits to encrypt *M* and refresh the bit sequences; in the simulation she may be directed to pick too few, and she and Bob share a signalling channel (which also goes through Eve, if she's present) so that they can restart the experiment if Alice doesn't have enough code bits. 

Restarting is not part of the QKD protocol. It would be a security risk, because Alice and Bob would have to re-use what should be one-time hash keys, and multiple re-use might give an eagle-eyed interceptor enough information to hack the classical channel. It's in the simulation just to allow experiment with calculating qbit numbers: see the [description of Alice's calculation](#enoughqbits) for an analysis of repetition frequency and see the [no Eve trials](#noEve) for some experimental results.

<a name="enoughqbits"></a>
## Picking enough qbits

Suppose Alice's message *M* is *m* bits long, and that the Wegman-Carter one-time hash keys are each *w* bits long, so she needs at least

&emsp;&emsp;*k* = *m*+5*w*

secret code bits: *m* to encrypt *M* and send it to Bob, 5*w* to use for new hash keys. if *n* is the number of qbits she sends, then she can expect that about *n*/2 code bits will be agreed with Bob, who will then take a proportion of those -- in our simulation a quarter or *n*/8 -- for check bits. So *n*/2 - *n*/8 = 3*n*/8 has to be at least *k*. (Actually she would probably have a minimum number *c* of checkbits in mind, to ensure that the quantum-interference check is reliable, so that puts a lower bound on *n*/8, but we can deal with that by putting a lower bound on *n* after we've calculated it.)

She must also allow for statistical variation: sometimes she and Bob will agree less, sometimes more, code bits. She knows that the standard deviation &sigma; of the number of successes when choosing with probability *p* from a sequence length *n* is &radic;<span style="text-decoration:overline;">&nbsp;*np*(1-*p*)&nbsp;</span>. She wants the probability of choosing too few bits to be very small, so she must over-estimate. If she wants to be *s* &sigma;s away from trouble, well into the tail of the normal distribution, she can write some equations. 

First, Bob may choose more than *n*/8 bits: he chooses a bit with probability 1/4 from a sequence length *n*/2, so the worst-case pick that she has to allow for is

&emsp;&emsp;*b* = *n*/8 + *s*&radic;<span style="text-decoration:overline;">&nbsp;*n*/2(1/4)(3/4)&nbsp;</span>   

&emsp;&emsp;&emsp;&ensp;= *n*/8 + *s*&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>

If *s* is large enough Bob won't pick more than that many bits very often: [famously](https://en.wikipedia.org/wiki/68–95–99.7_rule) for *s*=5 the chances are 0.00003%, and they go down about three orders of magnitude for every increase in *s* after that. So Alice can give herself a comfortable allowance by choosing *s*=8 or *s*=10, or whatever she likes.

Alice and Bob will agree on the measurement basis for a qbit with probability 1/2. There will be statistical variation in the number of bits they agree on, and she must make sure that the number she needs is in the tail of the normal distribution, *s* &sigma;s away from the mean. So she can calculate 

&emsp;&emsp;*n*/2 &ge; *k* + *b* + *s*&radic;<span style="text-decoration:overline;">&nbsp;*n*(1/2)(1/2)&nbsp;</span>

&emsp;&emsp;&emsp;&ensp;= *k* + *b* + *s*/2&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>

&emsp;&emsp;&emsp;&ensp;= *k* + *n*/8 + *s*(&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>+1/2)&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span> 

Taking the inequality as an equality, this is a quadratic in &radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>:

&emsp;&emsp;3/8*n* - *s*(&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>+1/2)&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span> - *k* = 0

One of the solutions of this equation is negative, so we ignore it; the positive solution is 

&emsp;&emsp;&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span> = 4/3(*qs* + &radic;<span style="text-decoration:overline;">&nbsp;(*qs*)<sup>2</sup> + 3*k*/2&nbsp;</span>)
&emsp;where *q* = &radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>+1/2

Tricky in integer arithmetic ... so we approximate *q* = 806/1000 and do a lot of rounding up, which means Alice wastes some effort, but not too much and, as you'd expect, she calculates about half a &sigma; too much padding. 

At this point Alice has to decide if she will get enough check-bits from Bob. She can be sure of

&emsp;&emsp;*c* = *n*/8 - *s*&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>&radic;<span style="text-decoration:overline;">&nbsp;*n*&nbsp;</span>

So, given a pre-arranged lower bound *cmin*, she can calculate a lower bound *nmin* from a quadratic in &radic;<span style="text-decoration:overline;">&nbsp;*nmin*&nbsp;</span>

&emsp;&emsp;*nmin*/8 - *s*&radic;<span style="text-decoration:overline;">&nbsp;3/32&nbsp;</span>&radic;<span style="text-decoration:overline;">&nbsp;*nmin*&nbsp;</span> - *cmin* = 0

&emsp;&emsp;&radic;<span style="text-decoration:overline;">&nbsp;*nmin*&nbsp;</span> = *s*&radic;<span style="text-decoration:overline;">&nbsp;3/2&nbsp;</span>+&radic;<span style="text-decoration:overline;">&nbsp;3*s*<sup>2</sup>/2+8*cmin*&nbsp;</span>

This is quite a large lower bound: e.g. with *cmin*=20, *s*=10, we have *nmin*=891. Once again, we approximate: &radic;<span style="text-decoration:overline;">&nbsp;3/2&nbsp;</span> is about 1225/1000.

The [no Eve trials](#noEve) show how many bits she uses for various values of *k*, *s* and *cmin*, and how it affects the repetition rate.

<a name="wegmancarter"></a>
## Wegman-Carter hash-tagging

For verisimilitude I implement hash tagging. But it doesn't make a difference: in the simulation Eve can either hack it perfectly ([clever Eve](#cleverEve) and [cleverer Eve](#superEve)) or she doesn't even try ([naive Eve](#naiveEve)).

The mechanism is this: for a hash-key size *w* pick a packet size *s* such that *s*&ge;*w* and 2<sup>*s*</sup>-1 is prime (though the simulation doesn't bother with the prime test). Divide the bit sequence to be hashed into packets size 2*s*; convert each packet to an integer; multiply by the hash key; mask with 2<sup>*s*</sup>-1 to reduce the size of the result; convert back to bit strings and concatenate. That will have reduced the size of the bit-string by half. Repeat until you have *s* bits or less, and that's the tag. 

<a name="noEve"></a>
## No Eve: just Alice and Bob

Trials to see if Alice picks enough qbits. Interference never detected because Eve isn't there: command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp SystemAB.qtp)

Note that in this simulation Bob doesn't know the length of *M*, still less the number of qbits Alice is going to send him. He reads qbits until he sees Alice's first message on the classical channel. Oh, the power of guarded sums!

### With hash tags

  * With Wegman-Carter tagging, the hash calculations (implemented in the qtpi functional language and therefore slowly interpreted) take ages.
  But it works: Bob and Alice agree that neither is spoofing classical messages.
  
        length of message? 4000
        length of a hash key? 12
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 100

        13456 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 0 repetition(s); average check bits 1687 minimum check bits 1598
        histogram of check-bit lengths
        [(1598,1);(1613,1);(1615,1);(1622,1);(1625,1);(1627,1);(1634,1);(1635,1);(1638,1);(1639,1);(1645,3);(1647,1);(1648,2);(1651,1
        );(1654,1);(1655,1);(1657,2);(1658,1);(1661,1);(1662,1);(1663,2);(1664,1);(1665,1);(1666,3);(1668,1);(1669,1);(1670,2);(1673,
        2);(1674,2);(1675,1);(1677,3);(1678,2);(1680,2);(1681,1);(1684,1);(1686,1);(1687,1);(1688,1);(1689,1);(1690,1);(1691,1);(1692
        ,2);(1694,1);(1696,3);(1698,1);(1701,1);(1703,3);(1705,1);(1707,1);(1709,3);(1710,2);(1711,1);(1713,2);(1715,1);(1717,3);(
        1718,1);(1719,1);(1720,1);(1722,1);(1723,1);(1724,1);(1727,1);(1729,2);(1736,2);(1737,1);(1738,2);(1741,1);(1749,1);(1754,1);
        (1758,1);(1761,1);(1790,1)]

        real	1m19.446s
        user	0m45.455s
        sys	0m0.525s
  
  * That's about 4 seconds for each trial, but it is nevertheless 1.3M qbit measures in 45 seconds. 
  * In experiments below I mostly choose zero-length keys so as to turn hashing off.
  
### 0 Sigma  
* Checking the *cmin* &rarr; *nmin* calculation, and the lower-bounding. It works.

        length of message? 1
        length of a hash key? 0
        minimum number of checkbits? 20
        number of sigmas? 10
        number of trials? 1
        with commentary (y/n)? n

        900 qbits
        all done: 0 interfered with; 1 exchanges succeeded; 0 failed; 0 repetition(s); 
        average check bits 125 minimum check bits 125
        histogram of check-bit lengths [(125,1)]

        real	0m25.482s
        user	0m0.037s
        sys	0m0.006s

* With a medium-length message we get about 20% repetition rate. This is less than expected but integer square root and rounding gives far too many bits with small number of &sigma;s: the analytical number of qbits is 266 but Alice uses 289.
  
        length of message? 100
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 100
        
        289 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 20 repetition(s); average check bits 35 minimum check bits 22
        histogram of check-bit lengths
        [(22,1);(23,1);(24,3);(25,4);(27,3);(28,2);(29,4);(30,5);(31,4);(32,5);(33,2);(34,8);(35,6);(36,7);(37,8);(38,3);(39,7);(40,4
        );(41,8);(42,4);(43,1);(44,2);(46,1);(47,1);(48,3);(49,1);(51,1);(55,1)]

        real	0m21.096s
        user	0m0.709s
        sys	0m0.017s

 * With a very short message we get even worse rounding: the analytical answer is 8 qbits and Alice uses 16. Oh well.

        length of message? 3
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 100
  
        16 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 3 repetition(s); average check bits 1 minimum check bits 0
        histogram of check-bit lengths [(0,11);(1,29);(2,27);(3,25);(4,5);(5,3)]

        real	0m21.335s
        user	0m0.086s
        sys	0m0.005s
 
  * With a longer message, and therefore many more qbits, it's possible to see that the calculation is working well enough. The repetition rate is 38%, and 2704 qbits is somewhere between the 2666 that a 0-&sigma; experiment should use (when we should see error rates about 35%) and the 2780 that a 1-&sigma; should use (when we should see about 12%). Over-estimation by Alice, mostly caused by using integer square roots, is making her over-cautious. Never mind. So far as Alice is concerned, the calculation works.
 
        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        2704 qbits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 379 repetition(s); average check bits 336 minimum check bits 277
        histogram of check-bit lengths
        [(277,1);(290,1);(291,1);(294,2);(295,2);(297,1);(298,1);(299,2);(300,3);(301,5);(302,4);(303,3);(304,2);(305,6);(306,10);(
        307,3);(308,7);(309,5);(310,13);(311,7);(312,8);(313,13);(314,8);(315,9);(316,9);(317,13);(318,5);(319,17);(320,17);(321,13);
        (322,20);(323,15);(324,13);(325,16);(326,15);(327,20);(328,19);(329,23);(330,27);(331,27);(332,21);(333,29);(334,22);(335,15)
        ;(336,27);(337,25);(338,23);(339,28);(340,21);(341,22);(342,19);(343,21);(344,21);(345,25);(346,21);(347,20);(348,20);(349,26
        );(350,18);(351,12);(352,14);(353,12);(354,14);(355,17);(356,8);(357,8);(358,15);(359,6);(360,8);(361,11);(362,6);(363,5);(
        364,8);(365,4);(366,4);(367,4);(368,4);(369,7);(370,3);(371,2);(372,2);(373,3);(374,2);(376,1);(377,3);(378,1);(379,2);(381,1
        );(382,1);(383,1);(394,1)]

        real	1m40.728s
        user	1m19.496s
        sys	0m0.992s
        
### 1 Sigma

  * Attempting to swamp the rounding errors by choosing a longer message but 1 &sigma;. The repetition rate about 0.2%, which is absurdly low. The analytical number of qbits is 2780, but Alice uses 2809, which explains the result.
  
        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 1
        number of trials? 1000

        2809 qbits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 19 repetition(s); average check bits 351 minimum check bits 297
        histogram of check-bit lengths
        [(297,1);(302,1);(304,1);(305,1);(306,1);(307,1);(309,1);(311,4);(312,1);(313,2);(314,2);(315,1);(316,3);(317,2);(318,7);(319
        ,4);(320,7);(321,5);(322,6);(323,6);(324,7);(325,4);(326,5);(327,8);(328,11);(329,11);(330,6);(331,11);(332,14);(333,13);(334
        ,16);(335,16);(336,11);(337,20);(338,27);(339,20);(340,14);(341,13);(342,21);(343,19);(344,26);(345,21);(346,25);(347,23);(
        348,21);(349,29);(350,29);(351,17);(352,22);(353,27);(354,19);(355,19);(356,23);(357,21);(358,21);(359,14);(360,15);(361,17);
        (362,16);(363,12);(364,17);(365,24);(366,19);(367,16);(368,20);(369,12);(370,10);(371,9);(372,12);(373,8);(374,13);(375,8);(
        376,5);(377,9);(378,7);(379,10);(380,6);(381,6);(382,2);(383,7);(384,4);(385,9);(386,4);(387,2);(388,2);(389,1);(390,1);(392,
        3);(393,3);(395,1);(396,2);(397,2);(399,1);(400,1);(402,1);(405,1);(406,1)]

        real	1m26.289s
        user	1m1.882s
        sys	0m0.729s
  
### 2 Sigma

* With a long message and oodles of trials and only 2 &sigmas; we see no repetitions. Enough already: Alice is over-cautious. Which is good: it proves that she can definitely choose enough qbits to run the protocol reliably.
* This test took an hour and 40 minutes. That's enough. I'm convinced.

        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 2
        number of trials? 100000

        3025 qbits per trial
        all done: 0 interfered with; 100000 exchanges succeeded; 0 failed; 0 repetition(s); average check bits 378 minimum check bits 302
        histogram of check-bit lengths
        [(302,1);(307,1);(308,1);(309,5);(310,3);(311,2);(312,1);(313,2);(314,5);(315,4);(316,2);(317,5);(318,7);(319,12);(320,12);(
        321,12);(322,12);(323,15);(324,25);(325,31);(326,26);(327,30);(328,34);(329,44);(330,63);(331,72);(332,81);(333,69);(334,90);
        (335,120);(336,152);(337,158);(338,166);(339,197);(340,247);(341,276);(342,311);(343,336);(344,409);(345,414);(346,472);(347,
        523);(348,582);(349,619);(350,641);(351,775);(352,781);(353,868);(354,894);(355,1010);(356,1020);(357,1143);(358,1226);(359,
        1276);(360,1371);(361,1453);(362,1483);(363,1479);(364,1705);(365,1650);(366,1766);(367,1838);(368,1885);(369,1922);(370,2012
        );(371,2061);(372,2100);(373,2064);(374,2116);(375,2173);(376,2224);(377,2254);(378,2156);(379,2168);(380,2221);(381,2221);(
        382,2014);(383,2155);(384,2069);(385,1962);(386,1951);(387,1921);(388,1752);(389,1863);(390,1768);(391,1702);(392,1573);(393,
        1567);(394,1537);(395,1496);(396,1368);(397,1225);(398,1144);(399,1170);(400,1088);(401,975);(402,916);(403,834);(404,790);(
        405,689);(406,632);(407,604);(408,592);(409,557);(410,507);(411,467);(412,367);(413,389);(414,309);(415,271);(416,236);(417,
        223);(418,218);(419,206);(420,164);(421,151);(422,127);(423,109);(424,99);(425,78);(426,71);(427,68);(428,57);(429,51);(430,
        43);(431,42);(432,35);(433,30);(434,19);(435,28);(436,16);(437,22);(438,11);(439,12);(440,10);(441,8);(442,8);(443,5);(444,1)
        ;(445,6);(446,5);(447,2);(448,2);(449,1);(450,2);(451,3);(452,2)]

        real	99m41.799s
        user	97m55.327s
        sys	0m31.425s
        
    
<a name="naiveEve"></a>
## Alice, Bob and naive Eve

This is the intervention everybody knows about. The quantum and classical channels that are connected to Alice in fact go to [Eve](#whyEve). She has quantum and classical channels connected to Bob. So she can potentially intervene on either of them, or just pass on messages from one to the other.

Eve knows the protocol, and she knows Alice's and Bob's implementation (but they don't know hers). Like Bob she doesn't need to know anything about *M* or *n*: she can read qbits until she sees Alice's first classical message. 

If she passes on the qbits she sees without measuring them, and passes on classical messages likewise, she is undectable, like a network node. If she measures the qbits before sending them, she will be detected with a probability of 1-1/2<sup>c</sup> where *c* is the number of checkbits Bob generates. If she tries to send messages on the classical channel, guessing the hash keys, she will be detected with a probability of 1-1/2<sup>5*w*</sup>. Because, with long messages and a suitably cautious Alice, *c* is probably >> 5*w*, most people have concluded that QKD's strength is in the quantum channel. Maybe not, as we shall see below.

Naive Eve does indeed measure and re-transmit the qbits she receives. She is, of course, pretty much always detected. Once she's spotted, Alice doesn't encrypt and send *M*, so even if Eve could hack the classical channel it wouldn't do her much good. In my simulation she simply re-transmits classical messages.

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
        naiveEve.qtp LogEve.qtp SystemAEB.qtp)

Note that the simulation runs the exact same Alice, Bob and their loggers as the Eve-free simulation did. The SystemAEB file runs Alice, Bob and naive Eve in parallel with their three loggers (though it's set up to deal with [cleverer Eve](#superEve), so naive Eve has to use two logging channels when she only really needs one).

  * Alice goes for super-safety in the number of qbits she uses. And then, of course, she detects interference _every_ time.
  
        length of message? 100
        length of a hash key? 0
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 100

        1156 qbits per trial
        all done: 0 Eve's; 100 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); 
        average check bits (Alice/Eve) 145; minimum check bits (Alice/Eve) 115; average check bits (Eve/Bob) 145; minimum check bits (Eve/Bob) 115
        histogram of check-bit lengths (Alice/Eve)
        [(115,1);(121,1);(125,1);(127,1);(128,1);(129,1);(130,2);(131,3);(132,3);(133,2);(134,1);(135,3);(136,1);(137,4);(138,3);(139
        ,3);(140,4);(141,3);(143,6);(144,5);(145,4);(146,2);(147,2);(148,4);(149,4);(150,3);(151,3);(152,4);(153,5);(154,2);(155,2);(
        157,4);(158,3);(159,2);(160,1);(163,1);(167,1);(171,1);(174,2);(177,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(115,1);(121,1);(125,1);(127,1);(128,1);(129,1);(130,2);(131,3);(132,3);(133,2);(134,1);(135,3);(136,1);(137,4);(138,3);(139
        ,3);(140,4);(141,3);(143,6);(144,5);(145,4);(146,2);(147,2);(148,4);(149,4);(150,3);(151,3);(152,4);(153,5);(154,2);(155,2);(
        157,4);(158,3);(159,2);(160,1);(163,1);(167,1);(171,1);(174,2);(177,1)]

<a name="cleverEve"></a>
## Alice, Bob and clever Eve

It occurred to me that it would be possible for Eve to stand between Alice and Bob, playing Bob to Alice and Alice to Bob, _if_ she could write properly-tagged messages on the classical channel. That's a very big if: 1/2<sup>5*w*</sup> and all that. But suppose that she was listening on a parabolic microphone in the park in Zurich when Alice told Bob the passphrase and the number of bits per key, and suppose that she intervenes in every one of their exchanges from the very first. Then, of course, she won't be detected by any of the means discussed above: there won't be any interference on the quantum channels Alice&rarr;Eve and Eve&rarr;Bob (supposing no littler Eves in the way) and she can tag her pretend-Alice and pretend-Bob messages just as if she were Alice or Bob. Because there are, in effect, two QKD protocols running in parallel (one Alice&harr;Eve and the other Eve&harr;Bob) the two sides won't use the same codes nor the same hash keys after the first run. But that's no problem: it's easy for Eve to remember 10*w* hash-key bits.

My first attempt at a clever Eve wasn't quite successful, although in the simulation she is never detected, she always reads and decrypts Alice's message and she always recrypts it for Bob. I haven't yet, for full verisimilitude, simulated the Wegman-Carter hashing mechanism but that doesn't take away Eve's achievement because, when I do, I'll get the exact same results.

Like naive Eve she doesn't need information about *M* or *n*. But Eve isn't clever enough (or rather, I wasn't clever enough). I thought that Alice would always use _all_ her code bits (less the ones she needs to keep for next time's hash keys) to encrypt the message she sends to Bob, so that Bob would expect a message that is as long as his code-bit sequence (take away the hash keys). If Eve agrees more code bits with Bob than she does with Alice then she is in trouble: Bob controls the number of code bits in QKD, and she can't get Alice to agree more code bits once they've exchanged bases. So in desperation she has to force Bob to restart the protocol. This is very unsatisfactory: as we saw above, it's easy for Alice to use so many qbits that retries are vanishingly unlikely. A partner who requests restarts ought perhaps to be suspected of being an Eve.

There is more. Because this Eve wants Alice&rarr;Eve to have the same number of code bits as Eve&rarr;Bob, the mask she fakes and sends to Alice selects sometimes many fewer, and sometimes many more, values than Bob would have asked for. So the histogram of check-bit-subsequence lengths doesn't look normal, and that's a dead giveaway.

The command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
        cleverEve.qtp LogEve.qtp SystemAEB.qtp)

  * With a long message and a safety-first Alice (10 &sigma;s) there are no retries. But Eve's check-bit sequences are anomalous: she generates a 50% wider histogram than Bob does. If I were Alice I'd suspect an Eve.
  
        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 10
        number of trials? 1000

        4096 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); 
        average check bits (Alice/Eve) 511; minimum check bits (Alice/Eve) 369; average check bits (Eve/Bob) 512; minimum check bits (Eve/Bob) 447
        histogram of check-bit lengths (Alice/Eve)
        [(369,1);(389,1);(391,1);(392,1);(395,1);(397,1);(399,2);(405,1);(406,1);(407,1);(408,2);(409,2);(410,2);(412,1);(413,1);(414
        ,2);(415,2);(417,3);(418,2);(419,1);(420,1);(422,2);(423,1);(424,3);(426,1);(427,2);(428,2);(429,2);(430,2);(431,2);(432,5);(
        433,2);(435,5);(436,1);(437,2);(438,2);(439,1);(440,1);(441,3);(442,1);(443,5);(444,2);(446,6);(447,3);(448,4);(449,4);(450,2
        );(451,6);(452,3);(453,4);(454,3);(455,3);(456,4);(457,3);(459,7);(460,1);(461,5);(462,9);(463,4);(464,3);(465,3);(466,1);(
        467,6);(468,2);(469,4);(470,10);(471,3);(472,7);(473,8);(474,7);(475,7);(476,3);(477,7);(478,6);(479,10);(480,7);(481,6);(482
        ,3);(483,6);(484,10);(485,7);(486,8);(487,4);(488,10);(489,6);(490,8);(491,9);(492,8);(493,9);(494,5);(495,10);(496,12);(497,
        9);(498,6);(499,9);(500,7);(501,9);(502,9);(503,7);(504,7);(505,7);(506,7);(507,11);(508,9);(509,7);(510,13);(511,11);(512,9)
        ;(513,6);(514,5);(515,7);(516,9);(517,8);(518,11);(519,6);(520,9);(521,10);(522,6);(523,9);(524,5);(525,14);(526,11);(527,12)
        ;(528,4);(529,9);(530,12);(531,7);(532,10);(533,8);(534,5);(535,7);(536,11);(537,9);(538,12);(539,11);(540,7);(541,9);(542,5)
        ;(543,8);(544,4);(545,8);(546,7);(547,3);(548,9);(549,5);(550,4);(551,13);(552,7);(553,10);(554,6);(555,6);(556,5);(557,3);(
        558,7);(559,7);(560,2);(561,3);(562,5);(563,3);(564,2);(565,5);(566,5);(568,3);(569,4);(570,4);(571,3);(572,4);(573,5);(574,1
        );(575,3);(576,4);(577,5);(578,4);(579,1);(581,5);(582,6);(583,3);(584,5);(586,2);(587,1);(588,1);(590,2);(591,3);(592,4);(
        593,1);(594,1);(595,1);(597,2);(598,2);(599,3);(600,3);(601,2);(602,1);(604,1);(606,1);(608,2);(611,1);(612,2);(614,2);(616,2
        );(618,1);(623,1);(629,1);(636,1);(641,1);(647,1);(649,1);(672,1);(685,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(447,1);(453,1);(454,1);(461,3);(462,1);(463,2);(464,2);(465,2);(466,2);(467,1);(468,3);(469,2);(470,4);(471,3);(472,3);(473
        ,2);(474,5);(475,4);(476,8);(477,4);(478,6);(479,6);(480,4);(481,5);(482,8);(483,8);(484,4);(485,4);(486,8);(487,12);(488,12)
        ;(489,8);(490,12);(491,9);(492,13);(493,9);(494,9);(495,13);(496,12);(497,17);(498,17);(499,13);(500,13);(501,16);(502,17);(
        503,11);(504,24);(505,18);(506,21);(507,21);(508,23);(509,28);(510,11);(511,18);(512,15);(513,20);(514,22);(515,21);(516,23);
        (517,20);(518,12);(519,19);(520,26);(521,22);(522,11);(523,15);(524,18);(525,13);(526,16);(527,16);(528,11);(529,21);(530,10)
        ;(531,15);(532,9);(533,9);(534,12);(535,12);(536,12);(537,6);(538,9);(539,8);(540,6);(541,10);(542,3);(543,8);(544,5);(545,7)
        ;(546,5);(547,5);(548,3);(549,6);(550,3);(551,6);(554,4);(555,2);(557,3);(558,1);(559,2);(560,2);(561,2);(562,2);(563,1);(565
        ,1);(566,2);(567,1);(573,1);(575,1);(593,1)]

        real	3m26.518s
        user	2m59.271s
        sys	0m1.839s

  * With a shorter message and a careless Alice (0 &sigma;s; no checkbit minimum) there are restarts, but no more from Eve than from Alice (Bob can't initiate them). So nothing to suspect here, were it not for the histogram. The shortest check-bit sequence that Bob generates is 19; Eve generates one of length 2, way, way outside the expected range. Bob goes up to 55, Eve to 67. Eve is bang to rights: Alice should nab her.
  
        length of message? 100
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        289 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 164 repetitions (Alice-Eve); 165 repetitions (Eve-Bob); 
        average check bits (Alice/Eve) 34; minimum check bits (Alice/Eve) 2; average check bits (Eve/Bob) 35; minimum check bits (Eve/Bob) 21
        histogram of check-bit lengths (Alice/Eve)
        [(2,1);(3,1);(4,2);(6,1);(7,1);(8,5);(9,3);(10,3);(11,2);(12,3);(13,9);(14,5);(15,6);(16,7);(17,12);(18,10);(19,15);(20,14);(
        21,23);(22,18);(23,22);(24,10);(25,30);(26,40);(27,28);(28,26);(29,32);(30,31);(31,38);(32,39);(33,42);(34,34);(35,29);(36,32
        );(37,40);(38,32);(39,31);(40,32);(41,38);(42,23);(43,31);(44,22);(45,29);(46,24);(47,16);(48,18);(49,17);(50,10);(51,8);(52,
        15);(53,6);(54,10);(55,4);(56,5);(57,4);(58,2);(59,4);(60,1);(61,1);(63,1);(65,1);(67,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(21,3);(22,1);(23,5);(24,7);(25,11);(26,20);(27,18);(28,33);(29,29);(30,42);(31,48);(32,66);(33,57);(34,66);(35,62);(36,82);
        (37,77);(38,64);(39,62);(40,43);(41,53);(42,31);(43,36);(44,18);(45,24);(46,18);(47,9);(48,4);(49,6);(50,2);(52,2);(58,1)]

        real	0m40.038s
        user	0m14.587s
        sys	0m0.179s

  * To give statistical variation full rein, I use a ridiculously short message and 0 &sigma;s. Alice provokes 33 repetitions and Eve more repetitions than trials. Bob should spot her, though Alice probably wouldn't: her histogram is silly but then so is Bob's.

        length of message? 3
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        16 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 45 repetitions (Alice-Eve); 544 repetitions (Eve-Bob); 
        average check bits (Alice/Eve) 2; minimum check bits (Alice/Eve) 0; average check bits (Eve/Bob) 2; minimum check bits (Eve/Bob) 0
        histogram of check-bit lengths (Alice/Eve) [(0,175);(1,157);(2,187);(3,160);(4,116);(5,93);(6,55);(7,31);(8,17);(9,6);(10,2);(11,1)]
        histogram of check-bit lengths (Eve/Bob) [(0,115);(1,247);(2,297);(3,194);(4,104);(5,34);(6,7);(7,2)]

        real	0m25.204s
        user	0m1.680s
        sys	0m0.038s
  

_Definitely_ no cigar.

<a name="superEve"></a>
## Alice, Bob and cleverer Eve

In the simulation I can make Alice careful or careless. In reality she will probably be careful, and generate far more code bits than she strictly needs. If she is careless or deliberately generates too few, she'll have to restart. So Eve shouldn't worry: just let Alice control things. Play Bob to Alice and Alice to Bob, confident that in either direction there will be plenty of code bits to deal with the *M* that Alice has in mind, or if not, a restart won't be totally unexpected.

So cleverer Eve doesn't fake a mask when dealing with Alice: instead she does exactly what Bob would do, selecting check bits with probability 1/4. And when dealing with Bob she's just another Alice, agreeing a code as he directs. There is a possibility, if Alice is deliberately careless, that sometimes Alice could agree enough code bits with Eve to encrypt *M* when Eve and Bob did not. In that case Eve would have to ask Bob to restart. But also in that case Alice would be likely to provoke restarts of her own. 

As a bonus, this Eve is easier to code. No faking, no irrational restarts, two internal parallel processes.

The command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
        superEve.qtp LogEve.qtp SystemAEB.qtp)

  * With cautious Alice and a long message, no restarts and so Eve hides perfectly. Her histogram is a bit wider than Alice's, but it's within normal limits because she is exactly playing Bob.
  
        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 10
        number of trials? 1000

        4096 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); 
        average check bits (Alice/Eve) 511; minimum check bits (Alice/Eve) 445; average check bits (Eve/Bob) 511; minimum check bits (Eve/Bob) 435
        histogram of check-bit lengths (Alice/Eve)
        [(445,1);(451,1);(452,1);(458,2);(459,1);(460,2);(461,1);(462,1);(463,2);(464,1);(465,2);(466,2);(467,2);(468,1);(469,2);(470
        ,1);(471,5);(472,3);(473,4);(474,5);(475,4);(476,8);(477,4);(478,3);(479,5);(480,5);(481,4);(482,6);(483,9);(484,6);(485,9);(
        486,10);(487,10);(488,16);(489,7);(490,12);(491,8);(492,14);(493,16);(494,13);(495,6);(496,11);(497,17);(498,16);(499,13);(
        500,15);(501,11);(502,20);(503,19);(504,19);(505,25);(506,16);(507,19);(508,22);(509,21);(510,27);(511,16);(512,19);(513,13);
        (514,16);(515,20);(516,22);(517,21);(518,17);(519,20);(520,12);(521,23);(522,12);(523,15);(524,14);(525,15);(526,14);(527,11)
        ;(528,18);(529,12);(530,10);(531,14);(532,14);(533,10);(534,10);(535,14);(536,14);(537,11);(538,9);(539,12);(540,7);(541,6);(
        542,7);(543,5);(544,6);(545,7);(546,2);(547,6);(548,3);(549,3);(550,3);(551,4);(552,3);(553,2);(554,2);(555,1);(556,5);(557,1
        );(558,1);(559,2);(560,1);(562,1);(564,1);(565,2);(567,1);(568,1);(576,1);(581,1);(587,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(435,1);(444,2);(446,1);(452,1);(457,1);(458,1);(459,3);(460,1);(461,2);(462,1);(463,3);(465,2);(466,5);(467,4);(468,5);(469
        ,5);(470,4);(471,2);(472,5);(473,3);(474,7);(475,6);(476,7);(477,3);(478,5);(479,10);(480,5);(481,5);(482,6);(483,4);(484,12)
        ;(485,6);(486,13);(487,9);(488,8);(489,11);(490,14);(491,10);(492,8);(493,16);(494,11);(495,15);(496,15);(497,13);(498,6);(
        499,22);(500,12);(501,16);(502,15);(503,15);(504,9);(505,20);(506,22);(507,15);(508,21);(509,16);(510,23);(511,21);(512,19);(
        513,20);(514,16);(515,17);(516,15);(517,17);(518,15);(519,14);(520,15);(521,7);(522,17);(523,20);(524,14);(525,12);(526,17);(
        527,12);(528,15);(529,12);(530,14);(531,20);(532,8);(533,9);(534,14);(535,14);(536,7);(537,13);(538,17);(539,14);(540,8);(541
        ,5);(542,7);(543,7);(544,6);(545,4);(546,8);(547,4);(548,4);(549,4);(550,4);(551,2);(552,1);(553,5);(554,3);(555,3);(556,2);(
        557,1);(559,3);(560,1);(561,1);(562,1);(565,3);(567,1);(568,1);(569,1);(571,1);(576,1)]

        real	3m33.965s
        user	3m10.751s
        sys	0m2.068s

  * With mad Alice and a shorter message Eve is still under cover. No more Bob restarts from her than Eve restarts from Alice. This time her histogram's a tiny bit narrower, but all within normal variation.

        length of message? 100
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        289 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 160 repetitions (Alice-Eve); 166 repetitions (Eve-Bob); 
        average check bits (Alice/Eve) 35; minimum check bits (Alice/Eve) 20; average check bits (Eve/Bob) 35; minimum check bits (Eve/Bob) 17
        histogram of check-bit lengths (Alice/Eve)
        [(20,1);(21,4);(22,4);(23,4);(24,3);(25,11);(26,21);(27,23);(28,30);(29,42);(30,37);(31,49);(32,57);(33,82);(34,79);(35,57);(
        36,72);(37,71);(38,63);(39,56);(40,45);(41,43);(42,39);(43,31);(44,23);(45,14);(46,11);(47,7);(48,9);(49,5);(50,2);(51,1);(52
        ,1);(53,3)]
        histogram of check-bit lengths (Eve/Bob)
        [(17,1);(20,3);(21,6);(22,2);(23,4);(24,5);(25,9);(26,18);(27,18);(28,21);(29,39);(30,41);(31,52);(32,42);(33,65);(34,68);(35
        ,82);(36,95);(37,64);(38,60);(39,63);(40,53);(41,35);(42,40);(43,25);(44,25);(45,22);(46,11);(47,11);(48,8);(49,5);(50,3);(51
        ,2);(52,1);(54,1)]

        real	0m30.447s
        user	0m15.929s
        sys	0m0.191s
        
  * With a ridiculously short message the same pattern: no more restarts for Bob than he should expect.
  
        length of message? 3
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        16 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 31 repetitions (Alice-Eve); 25 repetitions (Eve-Bob); 
        average check bits (Alice/Eve) 2; minimum check bits (Alice/Eve) 0; average check bits (Eve/Bob) 1; minimum check bits (Eve/Bob) 0
        histogram of check-bit lengths (Alice/Eve) [(0,104);(1,285);(2,283);(3,193);(4,92);(5,37);(6,3);(7,2);(9,1)]
        histogram of check-bit lengths (Eve/Bob) [(0,123);(1,270);(2,300);(3,180);(4,95);(5,26);(6,5);(8,1)]

        real	0m9.774s
        user	0m1.432s
        sys	0m0.030s
        
So cleverer Eve seems to have got away with it. With the checks that are described in BB84 she's invisible, given the very large initial assumption that she has prior knowledge of Alice and Bob's initial one-time hash keys.

But not qiute invisible. In these days of GPS clocks Alice and Bob could pore over their logs. Some of the exchanges will be slower than Alice would expect, because Eve provokes an extra restart. So perhaps between 9 and 9.30 every morning she can play mad Alice, Bob can report arrival times, and they can try to spot her. They'd better not do it over the network, because Eve will just report arrival times for her, and Alice will see the times she would get if Eve wasn't there. Bob should take a printout of his arrival times to that park in Zurich. At that point Eve should burn the code books and run: nobody is truly undetectable.

<a name="notreally"></a>
## - but probably not

Restarts are part of the simulation because I wanted to watch the statistical variation of the choice mechanisms. They wouldn't be part of a real implementation, because a restart exposes the one-time hash keys more than once. So Alice would go for a large number of &sigma;s and a large minimum number of checkbits, and things would work out as in the first cleverer Eve test above: that is, she would hide perfectly. It looks as if there is a security hole.

But Alice has cryptographers for friends. They tell her to try to smoke Eve out. Every now and then, preferably when she has many more than the mean number of code bits, she should send a message as long as _all_ her code bits (less the ones she needs to refresh the hash keys). If she's connected directly to Bob he won't stumble, because he will have the same number of code bits as she does. But if Eve is in the way then she is in trouble: she probably won't have agreed as many code bits with Bob as Alice has agreed with her. So she can either send Bob a shorter message or run away.

Regular repetitions of Alice's swamping message tactic would seem to be a perfect counter-measure to cleverer Eve. In reality she might not be finished: Alice and Bob have to compare notes. They can't do that online, because Eve or a friend of hers could spoof the comparisons (remember, Eve et al. know how Alice and Bob are programmed). If they do it offline, then all sorts of Le Carr&eacute;-ish scenarios suggest themselves. Maybe real-life Eve isn't finished yet.

But let's not be silly. Technically, there's a counter-measure, and no security hole. And I dreamed of being famous ...

<a name="whyEve"></a>
## Why "Eve"?

"Eve" from "eavesdropper"? I do hope so. Not, I hope, from any notion of females as deceptive.
