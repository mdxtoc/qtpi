(If you are reading the html version of this note, and the non-ASCII symbols like &rarr; &radic; and so on look funny in your browser, make sure it knows it's reading a UTF-8 file. I had that problem too.)

# Experiments with QKD

I've encoded QKD in qtpi, and played around with it. The simulation has taught me a lot. I thought for a while that [I had found a (tiny) security hole](#cleverEve), and then that [I had made it a little bigger](#superEve), then I thought that [I probably hadn't](#notreally), and then that I should [try it out](#whataboutit).

But actually [it's codswallop](#codswallop). My 'security hole' is the way the protocol is supposed to work, daisy-chaining A&harr;B, B&harr;C, ... Y&harr;Z. Obviously each of those components has to be trusted; obviously if any is dishonest the whole chain is compromised. The research community is well aware of the problem, and well on top of it. So egg on my face. But I enjoyed my experiments, and I enjoyed building a tool which could carry them out.

## The scenario

Alice has a message *M* which she wants to send to Bob. She has a quantum channel to him, and a [Wegman-Carter hash-tagged](#wegmancarter) two-way classical channel to him. She [calculates the number of qbits she will need](#enoughqbits), and sends them, one at a time and picking measurement basis and value for each at random, to Bob. Bob separately picks a random basis for each qbit, measures it in that basis, and records the results.

Then they do the QKD protocol dance: Alice sends the bases she chose to Bob through the classical channel and Bob sends the bases he chose back to Alice. They each select the subsequence of values for which they used the same basis, which will be about half of them, and throw the rest away. Now, supposing no interference with the qbits in transit, and no interference with the classical messages, they share the same sequence of code bits. Bob picks a subsequence of his code bits, sends a bit-mask to Alice to characterise it, and the subsequence itself. Alice looks at the corresponding subsequence of her own code bits: if they have the same code bits then the two subsequences should be identical, with probability 1-1/2<sup>*c*</sup>, where *c* is the number of bits Bob picks. If the subsequences differ, and nothing is wrong with the classical communication, then something has interfered with Alice's quantum transmissions.

If all seems ok Alice deletes Bob's checkbits from her code bits, takes a prefix of what's left to exclusive-or mask the message *M*, and sends it down the classical channel to Bob. Bob, having deleted his checkbits from his own code bits, takes a prefix of the same length as Alice's communication, exclusive-or's the two, and he can see *M*. 

<a name="hashsecret"></a>
Before the protocol started Alice and Bob shared a secret: five 'short' one-time hash keys, one for each of the five classical messages they exchange (bases A&rarr;B, bases B&rarr;A, bit-mask B&rarr;A, subsequence B&rarr;A, encrypted message A&rarr;B). Each classical message is tagged by a hash of the message controlled by the corresponding hash key, and each tag is checked by the recipient, who uses the same hash function and knows the same hash key. If the tags aren't as expected then something is spoofing messages on the classical channel. If all is ok when the protocol is over, Alice and Bob each take five new hash keys from the unused suffix of their code bits, and they are ready to run the protocol again. Crucially, the classical messages are sent in the clear, but the secret code bits are never disclosed, apart from the checkbit sequence sent by Bob.

If there is an eavesdropper Eve, then the quantum and classical channels lead through her. She must do her best to read the quantum traffic between Alice and Bob, and to intercept and alter classical messages, and do it all without being noticed.

In the simulation we log the steps of the protocol, so our Alice, Bob and Eve each have a classical bit-list channel back to a logging process. In reality Alice and/or Bob would fall silent if they detected interference, but in the simulation we complete each trial even if something seems to be wrong. So Alice sends a blank (zero-length) message instead of an encrypted *M* if she detects quantum-channel interference, and each of them keeps going even if they detect classical-channel interference. 

In the real world Alice would be sure to pick enough qbits to ensure near certainty that Bob can select enough check bits to reliably detect interference, and to give her enough code bits to encrypt *M* and refresh the bit sequences. In the simulation she may be directed to pick too few, and she and Bob share a signalling channel (which also goes through Eve, if she's present) so that they can restart the experiment if Alice doesn't have enough code bits. 

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

Tricky in integer arithmetic ... so we approximate *q* = 806/1000 and do a lot of rounding up, which means Alice wastes some qbits, but not too many. As you'd expect, she calculates about half a &sigma; too much padding. 

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

Wegman-Carter tagging is too computationally expensive whilst qtpi is a naively interpreted language. So I do something simpler, because I'm not simulating security against code-crackers. It's still a hash, and experiment shows that if Eve accidentally gets her keys muddled up, Alice and Bob notice.

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
  
  * That's about 4 seconds for each trial, but it is 1.3M qbits in 45 seconds. It is a quarter faster without hash tagging (zero-length keys turn it off) or, if you like, a third slower with hash tagging.

        length of message? 4000
        length of a hash key? 0
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 100

        13225 qbits per trial
        all done: 0 interfered with; 100 exchanges succeeded; 0 failed; 0 repetition(s); average check bits 1651 minimum check bits 1570
        histogram of check-bit lengths
        [(1570,1);(1583,2);(1592,1);(1593,3);(1595,2);(1600,1);(1603,1);(1605,1);(1606,1);(1608,3);(1609,1);(1612,1);(1613,2);(1615,1
        );(1618,1);(1619,3);(1620,1);(1621,1);(1625,1);(1626,1);(1630,1);(1631,3);(1633,1);(1636,2);(1638,1);(1639,2);(1640,1);(1641,
        1);(1642,2);(1643,2);(1646,3);(1647,1);(1652,1);(1655,4);(1656,1);(1657,1);(1659,2);(1661,2);(1662,1);(1664,2);(1665,2);(1667
        ,1);(1669,1);(1670,2);(1671,1);(1673,1);(1674,2);(1675,1);(1683,1);(1684,1);(1685,1);(1686,2);(1688,2);(1690,3);(1691,1);(
        1693,2);(1694,1);(1695,1);(1697,1);(1702,1);(1703,2);(1705,1);(1708,1);(1714,1);(1716,1);(1732,1);(1733,1);(1743,1)]

        real	1m11.076s
        user	0m37.433s
        sys	0m0.440s

  * Even though the hash tagging mechanism is affordable it's turned off in many of the experiments below.
  
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
        length of a hash key? 20
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 100

        trial number 1 quantum interference detected -- 152 check bits
        trial number 2 quantum interference detected -- 162 check bits
        ...
        trial number 100 quantum interference detected -- 176 check bits

        1369 qbits per trial
        all done: 0 Eve's; 100 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); 
        average check bits (Alice/Eve) 171; minimum check bits (Alice/Eve) 146; average check bits (Eve/Bob) 171; minimum check bits (Eve/Bob) 146
        histogram of check-bit lengths (Alice/Eve)
        [(146,1);(149,2);(151,2);(152,2);(153,1);(154,1);(155,1);(156,1);(157,1);(158,2);(160,4);(161,4);(162,4);(163,2);(164,1);(165
        ,4);(166,2);(167,8);(168,2);(169,1);(170,2);(171,4);(172,4);(173,5);(174,5);(176,2);(177,2);(178,2);(179,5);(180,3);(181,1);(
        182,4);(183,1);(186,3);(187,1);(189,3);(190,2);(192,1);(196,1);(197,1);(198,1);(204,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(146,1);(149,2);(151,2);(152,2);(153,1);(154,1);(155,1);(156,1);(157,1);(158,2);(160,4);(161,4);(162,4);(163,2);(164,1);(165
        ,4);(166,2);(167,8);(168,2);(169,1);(170,2);(171,4);(172,4);(173,5);(174,5);(176,2);(177,2);(178,2);(179,5);(180,3);(181,1);(
        182,4);(183,1);(186,3);(187,1);(189,3);(190,2);(192,1);(196,1);(197,1);(198,1);(204,1)]

        real	0m32.667s
        user	0m5.784s
        sys	0m0.083s

<a name="cleverEve"></a>
## Alice, Bob and clever Eve

It occurred to me that it would be possible for Eve to stand between Alice and Bob, playing Bob to Alice and Alice to Bob, _if_ she could write properly-tagged messages on the classical channel. That's a very big if: 1/2<sup>5*w*</sup> and all that. But suppose that she was listening on a parabolic microphone in the park in Zurich when Alice told Bob the passphrase and the number of bits per key, and suppose that she intervenes in every one of their exchanges from the very first. Then, of course, she won't be detected by any of the means discussed above: there won't be any interference on the quantum channels Alice&rarr;Eve and Eve&rarr;Bob (supposing no littler Eves in the way) and she can tag her pretend-Alice and pretend-Bob messages just as if she were Alice or Bob. Because there are, in effect, two QKD protocols running in parallel (one Alice&harr;Eve and the other Eve&harr;Bob) the two sides won't use the same codes nor the same hash keys after the first run. But that's no problem: it's easy for Eve to remember 10*w* hash-key bits.

My first attempt at a clever Eve is never detected, always reads and decrypts Alice's message and almost always recrypts it for Bob.

Like naive Eve she doesn't need information about *M* or *n*. But Eve isn't clever enough (or rather, I wasn't clever enough). I thought that Alice would always use _all_ her code bits (less the ones she needs to keep for next time's hash keys) to encrypt the message she sends to Bob, so that Bob would expect a message that is as long as his code-bit sequence (take away the hash keys). If Eve agrees more code bits with Bob than she does with Alice then she is in trouble: Bob controls the number of code bits in QKD, and she can't get Alice to agree more code bits once they've exchanged bases. So in desperation she has to force Bob to restart the protocol. This is very unsatisfactory: as we saw above, it's easy for Alice to use so many qbits that retries are vanishingly unlikely. Bob should realise that a partner who requests restarts ought  to be suspected of being an Eve.

There is more. Because this Eve wants Alice&rarr;Eve to have the same number of code bits as Eve&rarr;Bob, the mask she fakes and sends to Alice selects sometimes many fewer, and sometimes many more, values than Bob would have asked for. So the histogram of check-bit-subsequence lengths doesn't look normal, and that's a dead giveaway.

The command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                cleverEve.qtp LogEve.qtp SystemAEB.qtp)

  * With a long message and a safety-first Alice (20-bit hash keys; 10 &sigma;s) there are no retries. But Eve's check-bit sequences are anomalous: she generates a checkbit histogram more than twice as wide as Bob's. If I were Alice I'd suspect an Eve.
  
        length of message? 1000
        length of a hash key? 20
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 1000

        4489 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); 
        average check bits (Alice/Eve) 559; minimum check bits (Alice/Eve) 378; average check bits (Eve/Bob) 561; minimum check bits (Eve/Bob) 491
        histogram of check-bit lengths (Alice/Eve)
        [(378,1);(403,1);(426,1);(428,1);(429,1);(438,1);(444,1);(447,2);(450,1);(454,1);(455,1);(456,1);(457,1);(459,1);(462,1);(463
        ,1);(464,1);(465,1);(466,5);(468,2);(469,1);(470,2);(472,3);(473,1);(474,2);(475,1);(476,2);(477,1);(478,1);(479,3);(480,2);(
        481,1);(482,4);(483,4);(484,2);(485,2);(486,1);(487,3);(488,2);(490,1);(491,6);(492,6);(493,1);(494,3);(495,1);(496,3);(497,3
        );(498,2);(499,6);(500,6);(501,6);(502,3);(503,5);(504,5);(505,5);(506,5);(507,7);(508,4);(509,3);(510,1);(511,4);(512,1);(
        513,4);(514,2);(515,2);(516,9);(517,6);(518,2);(519,8);(520,6);(521,6);(522,8);(523,2);(524,7);(525,5);(526,6);(527,5);(528,4
        );(529,11);(530,7);(531,8);(532,9);(533,8);(534,8);(535,8);(536,15);(537,8);(538,5);(539,13);(540,5);(541,9);(542,6);(543,9);
        (544,10);(545,11);(546,4);(547,10);(548,7);(549,7);(550,15);(551,11);(552,8);(553,6);(554,12);(555,12);(556,8);(557,12);(558,
        8);(559,13);(560,5);(561,10);(562,9);(563,8);(564,6);(565,7);(566,12);(567,6);(568,7);(569,10);(570,6);(571,12);(572,9);(573,
        9);(574,6);(575,10);(576,3);(577,8);(578,8);(579,2);(580,4);(581,11);(582,10);(583,8);(584,6);(585,9);(586,4);(587,10);(588,8
        );(589,2);(590,8);(591,6);(592,5);(593,6);(594,5);(595,9);(596,7);(597,5);(598,7);(599,6);(600,8);(601,5);(602,3);(603,5);(
        604,8);(605,8);(606,7);(607,6);(608,7);(609,1);(610,5);(611,4);(612,6);(613,3);(614,3);(615,2);(616,1);(617,5);(618,3);(619,3
        );(620,4);(621,5);(622,3);(623,5);(624,4);(625,4);(626,2);(627,6);(628,1);(629,3);(630,6);(631,5);(632,5);(633,1);(634,2);(
        635,1);(636,5);(637,2);(638,2);(639,2);(640,1);(641,5);(642,1);(643,1);(644,2);(645,1);(646,1);(648,1);(649,1);(650,1);(651,3
        );(652,1);(656,1);(659,1);(661,2);(663,1);(664,3);(671,1);(673,1);(681,1);(684,1);(686,1);(688,1);(695,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(491,1);(500,1);(501,1);(503,1);(505,4);(506,1);(507,1);(511,2);(513,1);(514,2);(515,1);(516,1);(517,1);(518,2);(519,1);(521
        ,4);(522,1);(523,3);(524,6);(525,5);(526,5);(527,7);(528,9);(529,5);(530,9);(531,6);(532,5);(533,12);(534,6);(535,9);(536,5);
        (537,9);(538,10);(539,15);(540,9);(541,17);(542,9);(543,14);(544,16);(545,16);(546,9);(547,14);(548,15);(549,23);(550,14);(
        551,16);(552,16);(553,19);(554,11);(555,23);(556,27);(557,19);(558,20);(559,20);(560,17);(561,20);(562,15);(563,26);(564,20);
        (565,18);(566,14);(567,19);(568,16);(569,17);(570,22);(571,19);(572,12);(573,14);(574,12);(575,14);(576,18);(577,12);(578,16)
        ;(579,8);(580,6);(581,12);(582,17);(583,7);(584,7);(585,12);(586,7);(587,14);(588,9);(589,8);(590,6);(591,2);(592,8);(593,5);
        (594,5);(595,1);(596,8);(597,5);(598,3);(599,6);(600,4);(601,5);(602,1);(603,1);(604,4);(605,5);(606,1);(607,2);(608,4);(609,
        1);(610,3);(611,1);(612,1);(614,2);(615,2);(616,1);(617,2);(618,2);(623,1);(626,1)]

        real	3m51.001s
        user	3m22.925s
        sys	0m2.501s

  * With a shorter message and a careless Alice (0 &sigma;s; no hashing; no checkbit minimum) there are restarts, but no more from Eve than from Alice. So nothing to suspect here, were it not for the histogram. The shortest check-bit sequence that Bob generates is 19; Eve generates one of length 2, way, way outside the expected range. Bob goes up to 58, Eve to 67. Eve is bang to rights: Alice should nab her.
  
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

In the simulation I can make Alice careful or careless. In reality she will be careful, generating far more code bits than she is likely to need. If she were careless or deliberately generated too few, she'd have to restart the communication, using the same hash keys twice, and that's a security risk. So Eve shouldn't worry: just let Alice control things. Play Bob to Alice and Alice to Bob, confident that in either direction there will be plenty of code bits to deal with the *M* that Alice has in mind, or if not, a restart won't be totally unexpected.

So cleverer Eve doesn't fake a mask when dealing with Alice: instead she does exactly what Bob would do, selecting check bits with probability 1/4. And when dealing with Bob she's just another Alice, agreeing a code as he directs. There is a possibility, if Alice is deliberately careless, that sometimes Alice could agree enough code bits with Eve to encrypt *M* when Eve and Bob did not. In that case Eve would have to ask Bob to restart. But also in that case Alice would be likely to provoke restarts of her own. 

As a bonus, this Eve is easier to code. No faking, no irrational restarts, two internal parallel processes.

The command is

        (cd examples/BB84_QKD; time ../../Qtpi Alice.qtp Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                superEve.qtp LogEve.qtp SystemAEB.qtp)

  * With cautious Alice and a long message, no restarts and Eve hides perfectly -- and note that she's perfectly tagging her classical messages. Her histogram is a bit wider than Alice's, but it's within normal limits because she is exactly playing Bob.
  
        length of message? 1000
        length of a hash key? 20
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 1000

        4489 qbits per trial
        all done: 1000 Eve's; 0 Alice's; 0 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); 
        average check bits (Alice/Eve) 561; minimum check bits (Alice/Eve) 494; average check bits (Eve/Bob) 560; minimum check bits (Eve/Bob) 492
        histogram of check-bit lengths (Alice/Eve)
        [(494,1);(498,1);(502,1);(505,2);(506,1);(509,1);(510,1);(512,3);(513,1);(514,4);(515,2);(516,5);(517,4);(518,1);(519,1);(520
        ,2);(521,3);(522,5);(523,5);(524,8);(525,4);(526,4);(527,8);(528,1);(529,9);(530,8);(531,9);(532,11);(533,4);(534,8);(535,10)
        ;(536,19);(537,12);(538,8);(539,10);(540,5);(541,11);(542,10);(543,10);(544,16);(545,14);(546,17);(547,15);(548,11);(549,12);
        (550,20);(551,21);(552,19);(553,18);(554,19);(555,19);(556,13);(557,14);(558,20);(559,15);(560,18);(561,17);(562,16);(563,15)
        ;(564,15);(565,25);(566,20);(567,19);(568,17);(569,15);(570,12);(571,19);(572,15);(573,19);(574,14);(575,10);(576,17);(577,7)
        ;(578,14);(579,9);(580,12);(581,9);(582,9);(583,10);(584,11);(585,11);(586,11);(587,9);(588,10);(589,10);(590,9);(591,3);(592
        ,5);(593,3);(594,8);(595,5);(596,11);(597,7);(598,7);(599,3);(600,7);(601,5);(602,1);(603,2);(604,5);(605,3);(606,2);(607,2);
        (608,4);(609,4);(610,1);(613,2);(614,1);(615,1);(616,1);(617,1);(618,1);(621,1);(627,1);(628,1);(630,1);(635,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(492,1);(494,1);(496,2);(502,1);(505,1);(507,1);(508,1);(509,2);(510,1);(512,1);(513,1);(514,1);(515,1);(516,4);(517,1);(518
        ,2);(519,4);(520,9);(521,5);(522,4);(523,3);(524,4);(525,8);(526,5);(527,4);(528,9);(529,7);(530,7);(531,7);(532,6);(533,11);
        (534,10);(535,8);(536,11);(537,16);(538,12);(539,3);(540,12);(541,12);(542,9);(543,9);(544,17);(545,13);(546,10);(547,21);(
        548,19);(549,8);(550,18);(551,18);(552,9);(553,20);(554,20);(555,20);(556,19);(557,14);(558,14);(559,12);(560,33);(561,14);(
        562,11);(563,16);(564,15);(565,25);(566,7);(567,23);(568,24);(569,22);(570,14);(571,11);(572,12);(573,14);(574,19);(575,19);(
        576,8);(577,13);(578,9);(579,10);(580,16);(581,14);(582,11);(583,10);(584,8);(585,13);(586,8);(587,11);(588,14);(589,9);(590,
        7);(591,7);(592,6);(593,6);(594,5);(595,6);(596,2);(597,5);(598,4);(599,5);(600,4);(601,1);(602,3);(603,3);(604,1);(605,4);(
        606,5);(607,3);(608,3);(609,4);(610,2);(611,1);(612,1);(615,1);(616,2);(617,1);(623,1);(624,1);(627,1);(632,1);(642,1);(650,1
        )]

        real	4m4.922s
        user	3m35.276s
        sys	0m2.360s

  * With careless Alice (not enough qbits) and a shorter message Eve is still under cover: no more Bob restarts from her than Eve restarts from Alice. This time her histogram's a tiny bit narrower, but all within normal variation.

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

<a name="notreally"></a>
## Or maybe not ... but wait a minute

Restarts are part of the simulation because I wanted to watch the statistical variation of the choice mechanisms. They wouldn't be part of a real implementation, because a restart exposes the one-time hash keys more than once. So Alice would go for a large number of &sigma;s, long hash keys and a large minimum number of checkbits, and things would work out as in the first cleverer Eve test above: that is, she would hide perfectly. It looks as if there is a security hole.

But Alice has programmers for friends. They tell her to try to smoke Eve out. Every now and then she should send a message as long as _all_ her code bits (less the ones she needs to refresh the hash keys). If she's connected directly to Bob he won't stumble, because he will have the same number of code bits as she does. But if Eve is in the way then she is in trouble: she probably won't have agreed the same number of code bits with Bob as Alice has agreed with her. So she can either send Bob a different message or run away.

I've simulated this defence. Every four messages or so, choosing at random, Alice sees if she has more than the expected number *n*/2-*n*/8-5*w* of secret code bits. If so, she makes up a random message of the same length as her code-bit sequence and fires it at whoever is listening on the quantum channel. If it's Eve she has a small chance of having as many or more code bits, but that's not enough for a long life.

The command is

        (cd examples/BB84_QKD; time ../../Qtpi nr_Alice.qtp nr_Bob.qtp functions.qtp LogAlice.qtp LogBob.qtp 
                                                    nr_superEve.qtp LogEve.qtp SystemAEB.qtp)

  * The logging process plays the r&ocirc;le of the Zurich park. If the message that Bob logged is not the one that Alice logged, and neither of them logged quantum or classical interference, then it's an 'undetected corrupt message'. Alice should fire at Eve about 1/8 of the time, and Eve can only duck a small proportion. 116 hits out of about 125 shots: it seems that Eve is no longer undectable.
  
        length of message? 1000
        length of a hash key? 20
        minimum number of checkbits? 40
        number of sigmas? 10
        number of trials? 1000

        4489 qbits per trial
        all done: 884 Eve's; 0 Alice's; 116 undetected corrupt messages; 0 repetitions (Alice-Eve); 0 repetitions (Eve-Bob); 
            average check bits (Alice/Eve) 559; minimum check bits (Alice/Eve) 494; average check bits (Eve/Bob) 561; 
            minimum check bits (Eve/Bob) 498
        histogram of check-bit lengths (Alice/Eve)
        [(494,1);(497,2);(503,1);(504,1);(505,1);(506,1);(507,2);(508,1);(509,2);(511,1);(512,2);(513,3);(514,3);(515,1);(516,1);(517,5);
        (518,2);(519,5);(520,5);(521,5);(522,4);(523,5);(524,4);(525,5);(526,6);(527,9);(528,7);(529,8);(530,7);(531,9);(532,3);(533,4);(
        534,11);(535,9);(536,7);(537,10);(538,12);(539,11);(540,11);(541,14);(542,13);(543,21);(544,15);(545,17);(546,14);(547,18);(548,
        17);(549,17);(550,16);(551,13);(552,19);(553,15);(554,12);(555,13);(556,17);(557,22);(558,14);(559,20);(560,13);(561,15);(562,21)
        ;(563,23);(564,23);(565,15);(566,16);(567,21);(568,19);(569,18);(570,19);(571,15);(572,23);(573,12);(574,11);(575,13);(576,18);(
        577,8);(578,11);(579,7);(580,9);(581,14);(582,10);(583,7);(584,14);(585,10);(586,9);(587,9);(588,7);(589,3);(590,8);(591,5);(592,
        13);(593,3);(594,7);(595,4);(596,9);(597,7);(598,3);(599,3);(600,2);(601,2);(602,2);(603,1);(604,4);(605,1);(606,2);(608,2);(610,
        3);(611,3);(612,1);(613,2);(614,2);(615,1);(618,1);(620,1);(626,1)]
        histogram of check-bit lengths (Eve/Bob)
        [(498,2);(505,1);(506,1);(510,1);(511,1);(512,2);(513,1);(514,1);(515,3);(516,2);(517,2);(518,2);(520,6);(521,2);(522,1);(523,5);
        (524,5);(525,4);(526,5);(527,13);(528,11);(529,4);(530,7);(531,10);(532,7);(533,12);(534,5);(535,14);(536,9);(537,8);(538,11);(
        539,8);(540,12);(541,14);(542,16);(543,17);(544,14);(545,8);(546,9);(547,12);(548,18);(549,15);(550,11);(551,10);(552,14);(553,19
        );(554,18);(555,20);(556,22);(557,15);(558,11);(559,18);(560,18);(561,16);(562,19);(563,27);(564,18);(565,24);(566,25);(567,16);(
        568,14);(569,13);(570,18);(571,9);(572,14);(573,16);(574,14);(575,18);(576,20);(577,13);(578,22);(579,14);(580,16);(581,6);(582,7
        );(583,18);(584,13);(585,6);(586,11);(587,8);(588,9);(589,5);(590,6);(591,6);(592,4);(593,6);(594,4);(595,8);(596,4);(597,4);(598
        ,3);(599,4);(600,2);(601,4);(602,11);(603,2);(604,1);(605,6);(606,3);(607,1);(608,1);(609,1);(614,3);(616,1);(617,1);(618,2);(623
        ,2);(625,3);(627,1)]

        real	3m56.020s
        user	3m30.731s
        sys	0m2.580s

But is she detectable? If Alice is sending _real_ messages she'll be using less than all her code bits: the swamping messages will be some kind of fake, made up for the purpose of smoking out Eve. Eve knows how Alice works: she should invent similar swamping messages, send them to Bob at the same frequency as Alice swamps her, and make sure that the _real_ messages all arrive in the right order.  I haven't simulated this counter-counter measure.

If they looked at their own message statistics Bob and Alice would be unaware of Eve's presence: Bob will see swamping messages as often as he'd expect, and Alice will see a normal histogram of checkbit lengths. If they look at message logs Eve will be unmasked because the log of checkbit masks and lengths won't match, and nor will the occurrences of swamping messages. 

It seems likely that anything Alice can do online can be matched by Eve. So perhaps there isn't a realistic defence, unless there is a channel outside the protocol for comparing logs.

<a name="whataboutit"></a>
## But does the attack work in any implementations?

If an implementation of the protocol is careless about the secrecy of the initial hash keys, an Eve could be successful. If it is careless with secrecy in dealing with recovery from hardware crashes, then one could imagine that an Eve-collaborator could provoke Bob or Alice to crash and allow an Eve to intervene. I think I have to look at implementations to see if it's possible. If an attack is effective then, of course, I shall provoke greater secrecy in future implementations. Which won't be a bad thing.

<a name="codswallop"></a>
## Oh no it isn't

BB84 QKD is designed to daisy-chain A&harr;B, B&harr;C, ... Y&harr;Z. Breaking one of the links and inserting a new component, e.g. by making A&harr;E and E&harr;B  is of course possible, provided E knows the secret keys for that link, and can easily be transformed after the first iteration into two links with separate keys. That's how it's supposed to work. The problem is keeping the keys secret. In practice that may not be as difficult as I had thought it was, given privacy amplification techniques (see, for example, Renner and Wolf, _Unconditional Authenticity and Privacy from an Arbitrarily Weak Secret_).

So I was silly. I'm not going to delete this stuff, though I probably should (and then you would have to recover it from the commit history).
<a name="whyEve"></a>
## Why "Eve"?

"Eve" from "eavesdropper"? I do hope so. Not, I hope, from any notion of females as deceptive.
