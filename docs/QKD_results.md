(I've deleted the html version of this file because git's rendering of this file is superior to an html browser's. So it's available at  

    https://github.com/mdxtoc/qtpi/blob/master/docs/QKD_results.md  
    
But if you are reading this then you already know that ...)

# Experiments with QKD

I've encoded QKD in qtpi, and played around with it. The simulation has taught me a lot. I thought for a while that I had found a (tiny) security hole, and then that I had made it a little bigger, then I thought that I probably hadn't, and then that I should try it out.

But actually it was all codswallop. My 'security hole' involved Eve somehow knowing the secret hash codes that Alice and Bob share initially. But such an Eve is just an intermediate agent in the way the protocol is supposed to work, conecting A to B by daisy-chaining A&harr;E, E&harr;F, ... Y&harr;Z; Z&harr;B. Obviously each of the intermediate agents has to be trusted; obviously if any is dishonest the whole chain is compromised. The research community is well aware of the problem, and well on top of it. So egg on my face. 

## The scenario

Alice has a message *M* which she wants to send to Bob. She has a quantum channel to him, and a [Wegman-Carter hash-tagged](#wegmancarter) two-way classical channel to him. She [calculates the number of qbits she will need](#enoughqbits), and sends them, one at a time and picking measurement basis and value for each at random, to Bob. Bob separately picks a random basis for each qbit, measures it in that basis, and records the results.

Then they do the QKD protocol dance: Alice sends the bases she chose to Bob through the classical channel and Bob sends the bases he chose back to Alice. They each select the subsequence of values for which they used the same basis, which will be about half of them, and throw the rest away. Now, supposing no interference with the qbits in transit, and no interference with the classical messages, they share the same sequence of code bits. Bob picks a subsequence of his code bits, sends a bit-mask to Alice to characterise it, and the subsequence itself. Alice looks at the corresponding subsequence of her own code bits: if they have the same code bits then the two subsequences should be identical. If the subsequences differ, and nothing is wrong with the classical communication, then something has interfered with Alice's quantum transmissions. If the subsequences are the same, then *probably* there's been no interference.

If all seems ok Alice deletes Bob's checkbits from her code bits, takes a prefix of what's left to exclusive-or mask the message *M*, and sends it down the classical channel to Bob. Bob, having deleted his checkbits from his own code bits, takes a prefix of the same length as Alice's communication, exclusive-or's the two, and he can see *M*. 

<a name="hashsecret"></a>
Before the protocol started Alice and Bob shared a secret: five 'short' one-time hash keys, one for each of the five classical messages they exchange (bases A&rarr;B, bases B&rarr;A, checkbit-mask B&rarr;A, checkbits B&rarr;A, encrypted message A&rarr;B). Each classical message is tagged by a hash of the message controlled by the corresponding hash key, and each tag is checked by the recipient, who uses the same hash function and knows the same hash key. If the tags aren't as expected then something is spoofing messages on the classical channel. If all is ok when the protocol is over, Alice and Bob each take five new hash keys from the unused suffix of their code bits, and they are ready to run the protocol again. Crucially, the classical messages are sent in the clear, but the secret code bits are never disclosed, apart from the checkbit sequence sent by Bob.

If there is an eavesdropper Eve, then the quantum and classical channels lead through her. She must do her best to read the quantum traffic between Alice and Bob, and to intercept and alter classical messages, and do it all without being noticed.

In the simulation we log the steps of the protocol, so our Alice, Bob and Eve each have a classical bit-list channel back to a logging process. In reality Alice and/or Bob would fall silent if they detected interference, but in the simulation we complete each trial even if something seems to be wrong. So Alice sends a blank (zero-length) message instead of an encrypted *M* if she detects classical or quantum-channel interference. 

In the real world Alice would make sure to pick enough qbits to ensure high probability that Bob can select enough check bits to reliably detect interference, and to give her enough code bits to encrypt *M* and refresh the hash keys. In the simulation she may be directed to pick too few. If so she doesn't pick new hash keys, and she sends only as much of *M* as she can encode. In practice not picking new hash keys would somewhat compromise the security of the classical channel, but this simulation doesn't try to exploit that.

In the past the exchange would be restarted if Alice found herself with too few code bits. But the way I did it messed up the analysis of the results, so it no longer happens. 

<a name="enoughqbits"></a>
## Picking enough qbits

(Simplified, 2021/11/18, to deal with a fixed number of checkbits.)

Suppose Alice's message *M* is *m* bits long and the management have decided to use *c* checkbits and *w*-bit keys for the Wegman-Carter authentication. We know that there are five classical messages per trial, so she needs at least

&emsp;&emsp;*k* = *m*+*c*+5*w*

secret code bits: *m* to encrypt *M* and send it to Bob, *c* for checkbits, 5*w* to use for new hash keys. if *N* is the number of qbits she sends, then she can expect that about *N*/2 code bits will be agreed with Bob.

She must allow for statistical variation: sometimes she and Bob will agree fewer, sometimes more, code bits. She knows that the standard deviation &sigma; of the number of successes when choosing with probability *p* from a sequence length *n* is &radic;<span style="text-decoration:overline;">&nbsp;*np*(1-*p*)&nbsp;</span>. She wants the probability of choosing too few bits to be very small, so she must over-estimate. If she wants to be *s* &sigma;s away from trouble, well into the tail of the normal distribution, she can write some equations. 

Alice and Bob will agree on the measurement basis for a qbit with probability 1/2. So she can calculate 

&emsp;&emsp;*N*/2 &ge; *k* + *s*&radic;<span style="text-decoration:overline;">&nbsp;*N*(1/2)(1/2)&nbsp;</span>

&emsp;&emsp;&emsp;&ensp;= *k* + *s*/2&radic;<span style="text-decoration:overline;">&nbsp;*N*&nbsp;</span>

Taking the inequality as an equality, this is a quadratic in &radic;<span style="text-decoration:overline;">&nbsp;*N*&nbsp;</span>:

&emsp;&emsp;*N*/2 - *s*/2&radic;<span style="text-decoration:overline;">&nbsp;*N*&nbsp;</span> - *k* = 0

One of the solutions of this equation is negative, so we ignore it and take the positive solution: qtpi's *num* type includes both integers and unbounded-precision rationals, so she can calculate the root directly. (Of course we still use an approximation for *sqrt*.) 

The calculation so far isn't quite right, because Bob chooses checkbits at random from the *N*/2 that he and Alice share. If he chose with probability 2*c*/*N* he would get *c* checkbits *on average*. He wants the minimum -- i.e. the number which is *s*&sigma; away from the mean -- to be *c*. He has to shoot a little higher. A better guess would be 

&emsp;&emsp;*cmin* = *c*+*s*&radic;<span style="text-decoration:overline;">&nbsp;*c*&nbsp;</span>

-- possibly overkill, but safety first. But then we have to worry about Bob taking too many checkbits, and not leaving enough for Alice. So we ought to allow another *s*&radic;<span style="text-decoration:overline;">&nbsp;*c*&nbsp;</span> for that. At any rate, plug *cmax* in place of *c* in the quadratic above and we're likely to get the right number of checkbits.

The [no Eve trials](#noEve) show how many bits she uses for various values of *k*, *s* and *c*, and how it affects the repetition rate.

<a name="wegmancarter"></a>
## Wegman-Carter hash-tagging

For verisimilitude I implement hash tagging. But it doesn't make a difference: in the simulation Eve can either hack it perfectly ([clever Eve](#cleverEve)) or she doesn't even try ([naive Eve](#naiveEve)).

Wegman-Carter tagging seems too computationally expensive whilst qtpi is a naively interpreted language. So I do something simpler, because I'm not simulating security against code-crackers. It's still a hash, and experiment shows that if Eve accidentally gets her keys muddled up, Alice and Bob notice.

For a hash-key size *w* choose packet size *p* = *w*/3\*4+1. Divide the bit sequence to be hashed into packets size 2*p*; convert each packet to an integer; multiply by the hash key; mask with 2<sup>*p*</sup>-1 to reduce the size of the result; convert back to bit strings and concatenate. That will have reduced the size of the bit-string by half. Repeat until you have no more than *p* bits, and that's the tag. 

<a name="noEve"></a>
## No Eve: just Alice and Bob

Trials to see if Alice picks enough qbits. Interference never detected because Eve isn't there: command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                    SystemAB.qtp)

Note that in this simulation Bob doesn't know the length of *M*, still less the number of qbits Alice is going to send him. He reads qbits until he sees Alice's first message on the classical channel. Oh, the power of guarded sums!

### With hash tags

  * With hash tagging, the hash calculations are implemented in the qtpi functional language and therefore slowly interpreted.
  But it works: Bob and Alice each agree that the other isn't spoofing classical messages.
  
        length of message? 4000
        length of a hash key? 12
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 100

        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 0 short messages; 0 keys reused;
        average check bits  1664.61 minimum check bits 1562
        histogram of check-bit lengths
        [(1562,1);(1569,1);(1584,1);(1601,1);(1604,1);(1614,1);(1617,1);(1622,1);(1623,1);(1625,1);(1626,1);
        (1627,1);(1628,1);(1629,1);(1631,2);(1632,1);(1633,1);(1635,3);(1636,1);(1639,1);(1640,3);(1641,4);(
        1642,1);(1643,2);(1644,1);(1645,1);(1647,1);(1648,2);(1650,1);(1651,2);(1652,1);(1653,1);(1654,2);(
        1655,1);(1656,1);(1661,1);(1662,1);(1663,3);(1664,2);(1665,2);(1666,1);(1667,1);(1668,1);(1670,3);(
        1671,1);(1674,1);(1676,2);(1679,2);(1682,1);(1683,1);(1685,1);(1688,1);(1690,1);(1691,2);(1692,2);(
        1694,1);(1697,2);(1700,1);(1703,1);(1705,1);(1706,1);(1709,2);(1713,1);(1718,2);(1719,1);(1721,1);(
        1722,1);(1723,1);(1725,1);(1726,1);(1728,1);(1732,1);(1733,1);(1736,1);(1738,1)]

        real    1m18.732s
        user    0m48.742s
        sys 0m0.518s
  
  * That's about 5 seconds for each trial, but it is 1.3M qbits in 50 seconds. It is a fifth faster without hash tagging (zero-length keys turn hash tagging off) or, if you like, a quarter slower with hash tagging.

        length of message? 4000
        length of a hash key? 0
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 100

        13131 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 0 short messages; 0 keys reused; average check bits 1648.43 minimum check bits 1556
        histogram of check-bit lengths [(1556,1);(1578,1);(1586,1);(1588,2);(1594,1);(1596,1);(1601,1);(1604,1);(1605,1);(1610,1);(1614,2);(1615,5);(1616,2);(1617,1);(1620,2);(1621,1);(1622,2);(1623,3);(1625,6);(1628,2);(1630,1);(1632,1);(1634,2);(1635,1);(1636,1);(1637,2);(1641,2);(1642,1);(1644,2);(1645,1);(1650,1);(1651,2);(1652,1);(1653,1);(1654,2);(1655,1);(1656,1);(1657,1);(1659,2);(1660,1);(1661,1);(1664,1);(1666,1);(1667,1);(1669,1);(1670,2);(1672,1);(1673,2);(1674,3);(1675,1);(1679,1);(1682,1);(1683,1);(1684,1);(1687,1);(1688,1);(1689,3);(1691,1);(1693,1);(1695,1);(1701,1);(1703,1);(1704,1);(1712,4);(1720,1);(1721,1);(1734,1)]

        real	0m39.876s
        user	0m39.027s
        sys	0m0.415s

  * Even though the hash tagging mechanism is affordable it's turned off in many of the experiments below.
  
### 0 Sigma  
* Checking the *cmin* &rarr; *nmin* calculation, and the lower-bounding. It works, but note that with 0&sigma you can often get fewer checkbits than you asked for.

        length of message? 1
        length of a hash key? 0
        minimum number of checkbits? 20
        number of sigmas? 0
        number of trials? 100

        161 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 0 short messages; 0 keys reused;
        average check bits 20.23 minimum check bits 12
        histogram of check-bit lengths
        [(12,2);(13,2);(14,3);(15,5);(16,7);(17,11);(18,7);(19,9);(20,10);(21,5);(22,11);(23,4);(24,7);(25,5
        );(26,3);(27,5);(28,2);(29,1);(30,1)]

        real    0m14.853s
        user    0m0.525s
        sys 0m0.015s

* With a medium-length message, no minimum number of checkbiits and 0&sigma; we get a lot of short messages (not enough codebits to encrypt *M*). We always have enough codebits to refresh the hash keys, because there aren't any hash keys. 

        length of message? 100
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 100

        267 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 53 short messages; 0 keys reused;
        average check bits 32.94 minimum check bits 19
        histogram of check-bit lengths
        [(19,1);(23,1);(24,4);(25,1);(26,3);(27,4);(28,6);(29,8);(30,3);(31,10);(32,7);(33,7);(34,8);(35,5);
        (36,9);(37,4);(38,2);(39,5);(40,7);(41,2);(43,1);(45,1);(49,1)]

        real    0m0.891s
        user    0m0.853s
        sys 0m0.018s

* With small hash keys we allow enough leeway to almost always encrypt *M*, but quite often don't have enough codebits to generate new hash keys. 

        length of message? 100
        length of a hash key? 4
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 100

        321 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 1 short messages; 41 keys reused;
        average check bits 40.47 minimum check bits 25
        histogram of check-bit lengths
        [(25,1);(29,1);(30,1);(31,3);(32,4);(33,2);(34,3);(35,2);(36,9);(37,7);(38,7);(39,5);(40,7);(41,5);(
        42,8);(43,8);(44,4);(45,6);(46,2);(47,3);(48,1);(49,1);(50,2);(51,2);(52,4);(53,1);(55,1)]

        real    0m1.363s
        user    0m1.320s
        sys 0m0.021s
 
  * With a longer message, and therefore many more qbits, it's possible to see that the estimation of the number of qbits is working accurately. The short-message rate is ridiculous, but that's a consequence of using 0 sigmas. 
   
        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        2667 qbits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 488 short messages; 0 keys reused;
        average check bits 334.48 minimum check bits 281
        histogram of check-bit lengths
        [(281,1);(283,1);(285,1);(287,1);(288,2);(291,1);(292,2);(293,2);(294,3);(295,3);(296,4);(297,1);(
        299,3);(300,4);(301,3);(302,1);(303,4);(304,3);(305,5);(306,5);(307,10);(308,5);(309,7);(310,9);(311
        ,4);(312,12);(313,7);(314,8);(315,11);(316,15);(317,11);(318,11);(319,18);(320,22);(321,14);(322,13)
        ;(323,16);(324,33);(325,16);(326,23);(327,24);(328,20);(329,24);(330,22);(331,27);(332,29);(333,19);
        (334,33);(335,17);(336,18);(337,31);(338,22);(339,17);(340,27);(341,23);(342,21);(343,27);(344,15);(
        345,19);(346,10);(347,12);(348,27);(349,15);(350,15);(351,16);(352,18);(353,9);(354,11);(355,9);(356
        ,10);(357,11);(358,7);(359,9);(360,6);(361,8);(362,11);(363,2);(364,6);(365,6);(366,1);(367,2);(368,
        4);(369,3);(370,2);(371,4);(372,3);(375,2);(376,2);(377,1);(379,1);(380,1);(384,2);(385,1);(386,1);(
        387,1);(397,1)]

        real    1m19.995s
        user    1m18.108s
        sys 0m0.861s
        
### 1 Sigma

  * A longer message but 1 &sigma;. The short-message rate is about 0.4%, which seems rather low. 
  
        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 1
        number of trials? 1000

        2781 qbits per trial
        all done: 0 interfered with; 1000 exchanges succeeded; 0 failed; 41 short messages; 0 keys reused;
        average check bits 347.10 minimum check bits 294
        histogram of check-bit lengths
        [(294,1);(298,1);(301,3);(302,2);(303,2);(304,1);(306,3);(307,1);(308,3);(310,3);(311,2);(313,6);(
        314,3);(315,2);(316,7);(317,3);(318,4);(319,7);(320,6);(321,3);(322,9);(323,6);(324,13);(325,7);(326
        ,15);(327,15);(328,10);(329,12);(330,13);(331,17);(332,11);(333,19);(334,14);(335,20);(336,30);(337,
        25);(338,14);(339,15);(340,17);(341,19);(342,29);(343,31);(344,17);(345,21);(346,18);(347,27);(348,
        10);(349,24);(350,30);(351,19);(352,24);(353,30);(354,27);(355,18);(356,27);(357,19);(358,19);(359,
        13);(360,15);(361,12);(362,10);(363,27);(364,10);(365,17);(366,12);(367,13);(368,8);(369,10);(370,13
        );(371,12);(372,9);(373,3);(374,7);(375,6);(376,7);(377,5);(378,5);(379,4);(380,4);(381,6);(382,3);(
        383,4);(385,2);(386,1);(387,2);(388,1);(389,3);(392,1);(394,1)]

        real    1m23.901s
        user    1m21.833s
        sys 0m0.948s
  
### 3 Sigma

* With a reasonably long message and small oodles of trials and only 3 &sigma; we see no short messages. Enough already: Alice is over-cautious. Which is good: it proves that she can definitely choose enough qbits to run the protocol reliably.
* This test takes over 15 minutes. That's enough. I'm convinced.

        length of message? 1000
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 3
        number of trials? 10000

        3022 qbits per trial
        all done: 0 interfered with; 10000 exchanges succeeded; 0 failed; 0 short messages; 0 keys reused;
        average check bits 377.65 minimum check bits 315
        histogram of check-bit lengths
        [(315,1);(316,1);(320,1);(322,2);(323,1);(324,4);(325,6);(326,3);(327,2);(328,2);(329,5);(330,16);(
        331,9);(332,7);(333,8);(334,8);(335,17);(336,14);(337,17);(338,20);(339,19);(340,25);(341,29);(342,
        28);(343,32);(344,47);(345,44);(346,43);(347,59);(348,61);(349,65);(350,55);(351,73);(352,76);(353,
        90);(354,104);(355,100);(356,116);(357,104);(358,126);(359,130);(360,134);(361,163);(362,163);(363,
        172);(364,175);(365,182);(366,177);(367,161);(368,193);(369,211);(370,197);(371,206);(372,205);(373,
        239);(374,213);(375,207);(376,232);(377,219);(378,215);(379,201);(380,224);(381,207);(382,203);(383,
        220);(384,200);(385,201);(386,187);(387,198);(388,180);(389,168);(390,183);(391,172);(392,156);(393,
        135);(394,128);(395,161);(396,123);(397,126);(398,130);(399,114);(400,112);(401,105);(402,81);(403,
        77);(404,74);(405,58);(406,79);(407,58);(408,58);(409,46);(410,32);(411,38);(412,38);(413,35);(414,
        42);(415,24);(416,27);(417,21);(418,24);(419,14);(420,18);(421,10);(422,12);(423,9);(424,8);(425,9);
        (426,6);(427,8);(428,3);(429,5);(430,5);(431,3);(432,3);(437,1);(438,1);(440,2);(442,1);(446,1);(455
        ,1)]

        real    15m25.995s
        user    15m2.982s
        sys 0m9.305s
            
<a name="naiveEve"></a>
## Alice, Bob and naive Eve

This is the intervention everybody knows about -- intercept and resend. The quantum and classical channels that are connected to Alice in fact go to [Eve](#whyEve). She has quantum and classical channels connected to Bob. So she can potentially intervene on either of them, or just pass on messages from one to the other.

Eve knows the protocol, and she knows Alice's and Bob's implementation (but they don't know hers). Like Bob she doesn't need to know anything about *M* or *n*: she can read qbits until she sees Alice's first classical message. 

If she passes on the qbits she sees without measuring them, and passes on classical messages likewise, she is undetectable, like a network node. If she measures the qbits before sending them, she will be detected with a probability of 1-3/4<sup>c</sup> where *c* is the number of checkbits Bob generates. If she tries to send messages on the classical channel, guessing the hash keys, she will be detected with a probability of 1-1/2<sup>5*w*</sup>. 

My simulation of naive Eve does indeed measure and re-transmit the qbits she receives. She is, as a consequence, pretty much always detected. Once she's spotted, Alice doesn't encrypt and send *M*, so even if Eve could hack the classical channel it wouldn't do her much good. In my simulation naive Eve simply re-transmits classical messages.

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                    naiveEve.qtp LogEve.qtp SystemAEB.qtp)

Note that the simulation runs the exact same Alice, Bob and their loggers as the Eve-free simulation did. The SystemAEB file runs Alice, Bob and naive Eve in parallel with their three loggers.

* If Alice goes for super-safety in the number of qbits she uses, then she detects interference _every_ time in the short simulations I have time to run. Her chance of evading detection with 124 checkbits -- the minimum number used in this example -- is about 3*10<sup>-16</sup>.
  
        length of message? 100
        length of a hash key? 20
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 1000

        all done: 0 Eve's; 1000 Alice's; 0 successful evasions; 0 short messages; 0 keys reused; average
        check bits (Alice/Eve) 163.72; minimum check bits (Alice/Eve) 124; average check bits (Eve/Bob)
        163.72; minimum check bits (Eve/Bob) 124
        histogram of check-bit lengths (Alice/Eve)
        [(124,1);(128,1);(135,3);(136,1);(137,7);(138,5);(139,4);(140,5);(141,3);(142,8);(143,10);(144,12);(
        145,8);(146,14);(147,14);(148,14);(149,10);(150,18);(151,20);(152,22);(153,22);(154,26);(155,22);(
        156,28);(157,42);(158,31);(159,23);(160,27);(161,29);(162,33);(163,32);(164,40);(165,26);(166,39);(
        167,30);(168,29);(169,26);(170,26);(171,29);(172,16);(173,23);(174,22);(175,12);(176,19);(177,23);(
        178,20);(179,23);(180,19);(181,7);(182,16);(183,7);(184,13);(185,3);(186,7);(187,6);(188,4);(189,4);
        (190,3);(191,4);(192,2);(193,4);(195,2);(196,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(124,1);(128,1);(135,3);(136,1);(137,7);(138,5);(139,4);(140,5);(141,3);(142,8);(143,10);(144,12);(
        145,8);(146,14);(147,14);(148,14);(149,10);(150,18);(151,20);(152,22);(153,22);(154,26);(155,22);(
        156,28);(157,42);(158,31);(159,23);(160,27);(161,29);(162,33);(163,32);(164,40);(165,26);(166,39);(
        167,30);(168,29);(169,26);(170,26);(171,29);(172,16);(173,23);(174,22);(175,12);(176,19);(177,23);(
        178,20);(179,23);(180,19);(181,7);(182,16);(183,7);(184,13);(185,3);(186,7);(187,6);(188,4);(189,4);
        (190,3);(191,4);(192,2);(193,4);(195,2);(196,1)]
        histogram of evasions
        [(124,0);(128,0);(135,0);(136,0);(137,0);(138,0);(139,0);(140,0);(141,0);(142,0);(143,0);(144,0);(
        145,0);(146,0);(147,0);(148,0);(149,0);(150,0);(151,0);(152,0);(153,0);(154,0);(155,0);(156,0);(157,
        0);(158,0);(159,0);(160,0);(161,0);(162,0);(163,0);(164,0);(165,0);(166,0);(167,0);(168,0);(169,0);(
        170,0);(171,0);(172,0);(173,0);(174,0);(175,0);(176,0);(177,0);(178,0);(179,0);(180,0);(181,0);(182,
        0);(183,0);(184,0);(185,0);(186,0);(187,0);(188,0);(189,0);(190,0);(191,0);(192,0);(193,0);(195,0);(
        196,0)]

        real    1m29.229s
        user    1m26.344s
        sys 0m0.797s

 * If Alice sends short messages and doesn't care about statistical variation, Eve can occasionally win. (It's safe, in this simulation, to use zero-length hash tags so as to increase the effect of statistical variation, because Eve isn't programmed to interfere with the classical channel.)  
* Note that Eve wins in the sense of reading the message correctly and transmitting it on to Bob, only rarely. She is undetected, though corrupting the message, far more often -- almost half the time. But the settings are deliberately ridiculous, to provoke that kind of result.  
* The number of evasions is as predicted by analysis, where Eve has 75% chance of evading detection on each checkbit.

        length of message? 10
        length of a hash key? 0
        minimum number of checkbits? 0
        number of sigmas? 0
        number of trials? 1000

        27 qbits per trial
        all done: 25 Eve's; 562 Alice's; 438 successful evasions; 143 short messages; 0 keys reused; average
        check bits (Alice/Eve) 3.36; minimum check bits (Alice/Eve) 0; average check bits (Eve/Bob) 3.36;
        minimum check bits (Eve/Bob) 0
        histogram of check-bit lengths (Alice/Eve)
        [(0,33);(1,119);(2,190);(3,213);(4,204);(5,128);(6,59);(7,33);(8,15);(9,5);(10,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(0,33);(1,119);(2,190);(3,213);(4,204);(5,128);(6,59);(7,33);(8,15);(9,5);(10,1)]
        histogram of evasions [(0,33);(1,85);(2,108);(3,90);(4,64);(5,36);(6,15);(7,7);(8,0);(9,0);(10,0)]

        real    0m2.611s
        user    0m2.517s
        sys 0m0.047s

## No more witnesses, m'lud

In earlier versions of this document I searched for ways to hide an Eve who knows the Wegman-Carter hash codes from a vigilant Alice and Bob. That was silly, so I deleted it.

<a name="whyEve"></a>
## Why "Eve"?

"Eve" from "eavesdropper"? I do hope so. Not, I hope, from any notion of females as deceptive.
