tpcat
=====

A quick and DIRTY fork of tpcat from EFF and beyond.  See https://www.eff.org/pages/pcapdiff and http://sourceforge.net/projects/tpcat/.

> TPCAT is based upon pcapdiff by the EFF. TPCAT will analyze two packet captures (taken on each side of the firewall as an example) and report any packets that were seen on the source capture but didn’t make it to the dest.

I just removed the requirement for wx and replaced it with argparse and printing to a broken html.  (Stupid, talk about a barrier to entry).  The goal here was to see how useful this tool was to our TCP/HTTP network analysis workflow.

requirements
============
https://pypi.python.org/pypi/pure-pcapy


