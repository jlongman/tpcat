##########################################################
##########################################################
# TPCAT Written by Tim Eberhard
# Requires wxpython, pcapy & Python 2.5
# For bugs or feature additions please contact:
# xmin0s@gmail.com
# Most of the pcapdiff code was written by Seth Schoen <schoen@eff.org> and Steven Lucy <slucy@parallactic.com> all such credit goes to them.
# I just wrote a basic front end and re-wrote some of their code to make it work within a class.
#
##########################################################
from __future__ import division
import os, re, sys, math, string, operator
import pcapy,
import binascii
import wx

import wx.richtext as rt
import wx.lib.filebrowsebutton as filebrowse
import time, sets


####################################################
TPCAT_Version = "Build 2.2"
####################################################

wildcard3 =  "Pcap Files (*.pcap)|*.pcap|"    \
          "All files (*.*)|*.*"           

wildcard2 =  "Text Files (*.txt)|*.txt|"    \
            "All files (*.*)|*.*"           
#Our protocol list
protocol = {0:" HOPOPT ", 1: "ICMP", 2: "IGMP", 3: "GGP ", 4: "IP ", 5: "ST ", 6: "TCP ", 7: "CBT ", 8: "EGP ", 9: "IGP ", 10: "BBN-RCC-MON ", 11: "NVP-II ", 12: "PUP ", \
13: "ARGUS ", 14: "EMCON ", 15: "XNET ", 16: "CHAOS ", 17: "UDP ", 18: "MUX ", 19: "DCN-MEAS ", 20: "HMP ", 21: "PRM ", 22: "XNS-IDP ", 23: "TRUNK-1 ", 24: "TRUNK-2 ", \
25: "LEAF-1 ", 26: "LEAF-2 ", 27: "RDP ", 28: "IRTP ", 29: "ISO-TP4 ", 30: "NETBLT ", 31: "MFE-NSP ", 32: "MERIT-INP ", 33: "DCCP ", 34: "3PC ", 35: "IDPR ", 36: "XTP ", \
37: "DDP ", 38: "IDPR-CMTP ", 39: "TP++ ", 40: "IL ", 41: "IPv6 ", 42: "SDRP ", 43: "IPv6-Route ", 44: "IPv6-Frag ", 45: "IDRP ", 46: "RSVP ", 47: "GRE ", 48: "DSR ", \
49: "BNA ", 50: "ESP ", 51: "AH ", 52: "I-NLSP ", 53: "SWIPE ", 54: "NARP ", 55: "MOBILE ", 56: "TLSP ", 57: "SKIP ", 58: "IPv6-ICMP ", 59: "IPv6-NoNxt ", 60: "IPv6-Opts ", \
61: "any ", 62: "CFTP ", 63: "any ", 64: "SAT-EXPAK ", 65: "KRYPTOLAN ", 66: "RVD ", 67: "IPPC ", 68: "any ", 69: "SAT-MON ", 70: "VISA ", 71: "IPCV ", 72: "CPNX ", \
73: "CPHB ", 74: "WSN ", 75: "PVP ", 76: "BR-SAT-MON ", 77: "SUN-ND ", 78: "WB-MON ", 79: "WB-EXPAK ", 80: "ISO-IP ", 81: "VMTP ", 82: "SECURE-VMTP ", 83: "VINES ", \
84: "TTP ", 85: "NSFNET-IGP ", 86: "DGP ", 87: "TCF ", 88: "EIGRP ", 89: "OSPFIGP ", 90: "Sprite-RPC ", 91: "LARP ", 92: "MTP ", 93: "AX.25 ", 94: "IPIP ", 95: "MICP ", \
96: "SCC-SP ", 97: "ETHERIP ", 98: "ENCAP ", 99: "any ", 100: "GMTP ", 101: "IFMP ", 102: "PNNI ", 103: "PIM ", 104: "ARIS ", 105: "SCPS ", 106: "QNX ", 107: "A/N ", \
108: "IPComp ", 109: "SNP ", 110: "Compaq-Peer ", 111: "IPX-in-IP ", 112: "VRRP ", 113: "PGM ", 114: "any ", 115: "L2TP ", 116: "DDX ", 117: "IATP ", 118: "STP ", \
119: "SRP ", 120: "UTI ", 121: "SMP ", 122: "SM ", 123: "PTP ", 124: "ISIS over IPv4 ", 125: "FIRE ", 126: "CRTP ", 127: "CRUDP ", 128: "SSCOPMCE ", 129: "IPLT ", \
130: "SPS ", 131: "PIPE ", 132: "SCTP ", 133: "FC ", 134: "RSVP-E2E-IGNORE ", 135: "Mobility Header  ", 136: "UDPLite ", 137: "MPLS-in-IP ", \
138-252: "Unassigned ", 253: "Use for experimentation and testing ", 254: "Use for experimentation and testing ", 255: "Reserved"}    

#TCP Flags for later use
flags_x = {0x02: "syn", 0x40: "reset", 0x11:"fin ack", 0x10: "ack", 0x12: "syn ack", 0x18: "psh ack"}
tcp_flags = {02: "syn", 40: "", 11:"fin ack", 10: "ack", 12: "syn ack", 18: "psh ack"}


#Standard Time stamp
Timestamp = time.strftime("%H:%M:%S",time.localtime())
Time_tpcat = "yes"
sync_paks  = "True"
#out_of_sync = 0
#########################
########GUI CODE###########
#########################


class MyFrame(wx.Frame):
    pcap_local = None
    pcap_remote = None
    ip_remote = None
    ip_local = None
    v = 0 #verbosity level
    ignore_tcp_checksum = 1
    ignore_timestamps = 0
    out_of_sync = 0
    skew_clocks = 0
    skew_amount = 0
    Time_tpcat = "false"
    debugfile = list()
    manifest = {}
    total = {}
    total['local'] = 0
    total['local_received'] = 0
    total['remote'] = 0
    total['remote_received'] = 0
    total['duplicates'] = 0
    debug = None
    def __init__(self, parent, title):
        wx.Frame.__init__(self, parent, -1, title, pos=(150, 150), size=(600, 400))

#Some basic settings that have to be handled out of the gate..
		#For quick and easy testing
        #self.pcap_remote = None #pcapy.open_offline('1805_pc.pcap')
        #self.pcap_local = None #pcapy.open_offline('791_pc.pcap')
        self.ip_local = '0.0.0.0'
        self.ip_remote = '0.0.0.0'
		
		
		
		
		
        #Menu bar at the top. File, edit and help.
        menuBar = wx.MenuBar()
        menu = wx.Menu()
        menu2 = wx.Menu()
        menu3 = wx.Menu()
        menu.Append(200, "Save Output..", "Save Output")
        menu.Append(wx.ID_EXIT, "E&xit\tAlt-X", "Exit")
        menu2.Append(300, "Copy", "Copy")
        menu2.Append(400, "Clear Buffer", "Clear Buffer")
        menu3.Append(100, "About", "About")
        self.Bind(wx.EVT_MENU, self.OnTimeToClose, id=wx.ID_EXIT)
        self.Bind(wx.EVT_MENU, self.message, id=100)
        self.Bind(wx.EVT_MENU, self.SaveFile, id=200)
        self.Bind(wx.EVT_MENU, self.OnCopy, id=300)
        self.Bind(wx.EVT_MENU, self.ClearBuffer, id=400)
        menuBar.Append(menu, "&File")
        menuBar.Append(menu2, "&Edit")
        menuBar.Append(menu3, "&Help")
        self.SetMenuBar(menuBar)
        self.CreateStatusBar()


        #Creates the base panel for us to work out of
        panel = wx.Panel(self, -1)
        buttons = wx.BoxSizer(wx.HORIZONTAL)

        #Here we have our pcap loaders. A simple load file dialog
        text2 = wx.StaticText(panel, -1, 'Please load your Pcap files:')
        self.fbb = filebrowse.FileBrowseButton(
            panel, -1, size=(450, -1), fileMask=wildcard3, changeCallback = self.fbbCallback
        )
        self.fbb2 = filebrowse.FileBrowseButton(
            panel, -1, size=(450, -1), fileMask=wildcard3, changeCallback = self.fbbCallback2
        )


        #A few input options for Source/Dest IP's
        l1 = wx.StaticText(panel, -1, "Source IP Address (Required):")
        t1 = wx.TextCtrl(panel, -1, "", size=(100, -1))
        t1.Bind(wx.EVT_TEXT, self.localip, t1)
        l2 = wx.StaticText(panel, -1, "Destination IP Address (Required):")
        t2 = wx.TextCtrl(panel, -1, "", size=(100, -1))
        t2.Bind(wx.EVT_TEXT, self.remoteip, t2)






        #Our Options
        #This options don't DO anything per say yet. I still need to have them trigger the various options.
        sb = wx.StaticBox(panel, -1, "Filter Options (Optional)")
        self.cb3 = wx.CheckBox(panel, -1, "Calculate Latency")
        self.cb5 = wx.CheckBox(panel, -1, "Sync the starting point of the two captures")
        self.cb6 = wx.CheckBox(panel, -1, "Record how long tpcat takes to analyze")
        self.cb2 = wx.CheckBox(panel, -1, "Debug (Ignore me unless you find a bug)")
        
        
        # Setup the layout
        box = wx.StaticBoxSizer(sb, wx.VERTICAL)
        box.Add(self.cb2, 0, wx.ALL, 5)
        box.Add(self.cb3, 0, wx.ALL, 5)
        #box.Add(cb4,   0, wx.ALL, 5)
        box.Add(self.cb5,   0, wx.ALL, 5)
        box.Add(self.cb6,   0, wx.ALL, 5)


        #self.Bind(wx.EVT_CHECKBOX, self.OnChecksum, self.cb2)
        self.Bind(wx.EVT_CHECKBOX, self.OnTimestamps, self.cb3)
        #self.Bind(wx.EVT_CHECKBOX, self.OnSkewclocks, cb4)
        self.Bind(wx.EVT_CHECKBOX, self.OnVbutton1, self.cb5)
        self.Bind(wx.EVT_CHECKBOX, self.OnVbutton2, self.cb6)
        self.Bind(wx.EVT_CHECKBOX, self.OnDebug, self.cb2)

        #And our Analyze button. This triggers the magic
        buttons = wx.BoxSizer(wx.HORIZONTAL)
        cb1 = wx.Button(panel, -1, "Analyze Pcap Files")
        cb10 = wx.Button(panel, -1, "Clear Buffer")
        buttons.Add(cb1, flag=wx.ALL, border=5)
        buttons.Add(cb10, flag=wx.ALL, border=5)
        
        pcap1 = self.pcap_local
        pcap2 = self.pcap_remote
        cb1.Bind(wx.EVT_BUTTON, self.pcapdiff)
        cb10.Bind(wx.EVT_BUTTON, self.ClearBuffer)


        self.rtxtctrl = rt.RichTextCtrl(panel, -1,
                                        "",size=(565, 625), style=wx.TE_MULTILINE)


        #Placement of all the garbage above. 
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(box, 0, wx.ALL, 15)
        #sizer.Add((15,15))
        sizer.Add(l1, 0, wx.ALL)
        sizer.Add(t1, 0, wx.ALL)
        sizer.Add(l2, 0, wx.ALL)
        sizer.Add(t2, 0, wx.ALL)
        sizer.Add(text2, 0, wx.ALL, 10)
        sizer.Add(self.fbb, 0, wx.ALL, 10)
        sizer.Add(self.fbb2, 0, wx.ALL, 10)
        sizer.Add(cb1, 0, wx.ALL, 10)
        sizer.Add(cb10, 0, wx.ALL, 10)
        sizer.Add(self.rtxtctrl, 2, wx.ALL, 10)
        panel.SetAutoLayout(True)
        panel.SetSizer(buttons)
        buttons.Fit(panel)
        panel.Move((50,50))
        
        panel.SetSizer(sizer)
        panel.Layout()

    def OnVbutton1(self, evt):
        self.out_of_sync = 0
        if self.cb5.IsChecked():
            self.out_of_sync = 1
            
    def OnVbutton2(self, evt):
        self.Time_tpcat = "no"
        if self.cb6.IsChecked():
            self.Time_tpcat = "yes"
            
    def OnChecksum(self, evt):
        self.ignore_tcp_checksum = 0
        
    def OnTimestamps(self, evt):
        self.ignore_timestamps = 0
        if self.cb3.IsChecked():
            self.ignore_timestamps = 1     
            
    def OnSkewclocks(self, evt):
        self.skew_clocks = 1
        
    def OnDebug(self, evt):
        self.debug = "no"
        if self.cb2.IsChecked():
            self.debug = "debug"  


    def OnCopy(self, evt):
        self.do = wx.TextDataObject()
        self.do.SetText(self.rtxtctrl.GetValue())
        if wx.TheClipboard.Open():
            wx.TheClipboard.SetData(self.do)
            wx.TheClipboard.Close()
        else:
            nothing = "null"                

        #Our little helpers:
    def SaveFile(self, evt):
        dlg = wx.FileDialog(
            self, message="Save file as ...", defaultDir=os.getcwd(), 
            defaultFile="", wildcard=wildcard2, style=wx.SAVE
        )

        dlg.SetFilterIndex(2)
        sfile = self.rtxtctrl.GetValue()
        if dlg.ShowModal() == wx.ID_OK:
            path = dlg.GetPath()
            fp = file(path, 'w') # Create file anew
            fp.write(sfile)
            fp.close()

        dlg.Destroy()



    def ClearBuffer(self, event):
        self.rtxtctrl.Clear()    


    def message(self, evt):
        msg = "TPCAT - Tim's Packet Capture Analysis Tool \n\n" + \
            "Author: Tim Eberhard \n\n" + \
            TPCAT_Version+"\n\n" + \
            "Please report any bug/requests or improvements\n" + \
            "To me at the following adresses:\n\n" + \
            "xmin0s@gmail.com\n\n" + \
            "Most of the pcapdiff code was written by Seth Schoen <schoen@eff.org>\n"  +\
            "and Steven Lucy <slucy@parallactic.com> and all such credit goes to them.\n\n"
        dlg = wx.MessageDialog(self, msg, "Tim Eberhard's TPCAT",
                               wx.OK | wx.ICON_INFORMATION)
        dlg.SetFont(wx.Font(8, wx.NORMAL, wx.NORMAL, wx.NORMAL, False, "Verdana"))
        dlg.ShowModal()
        dlg.Destroy()

        
    def localip(self, event):
        ip_local2 = "%s\n" % event.GetString()    
        self.ip_local = str(ip_local2.strip())
        #self.rtxtctrl.WriteText("Local IP: %s\n" %(ip_local)) #For Debug use only
    def remoteip(self, event):
        ip_remote2 = "%s\n" % event.GetString()    
        self.ip_remote = str(ip_remote2.strip())
        #self.rtxtctrl.WriteText("Remote IP: %s\n" %(ip_remote)) #For Debug use only

#Fbbcallback saves the pcap files loaded to memory
    def fbbCallback(self, evt):
        if hasattr(self, 'fbb'):
            self.pcap_file = evt.GetString()


    def fbbCallback2(self, evt):
        if hasattr(self, 'fbb'):
            self.pcap_file2 = evt.GetString()



    def dbbCallback(self, evt):
        self.log.write('DirBrowseButton: %s\n' % evt.GetString())


        #Our exit function   
    def OnTimeToClose(self, evt):
        """Event handler for the button click."""
        self.Close()

#######################################################################
#######################################################################
##########################Start Pcapdiff code##################################
#######################################################################
#######################################################################



    def print_saved_packet(self, spacket):
        '''
        Print out a packet saved with parse_and_save
        '''

        s = packet_to_string(spacket)
        if s:
            print '------------'
            print s

    def packet_to_string(self, spacket, hidefields=0):
        '''
        Take a saved packet, dump out a string.
        Optional argument tells it to hide fields that might change between
        two hosts, e.g. ip_ttl
        '''

        s = '' # to be returned

        fields = 'timestamp eth_type eth_dest eth_src ip_version ip_header_length ip_tos ip_total_length ip_ident ip_flags ip_ttl ip_protocol ip_header_checksum ip_src ip_dest ip_options ip_payload_length ip_payload_data tcp_port_pair tcp_sequence_number tcp_sequence_diff'.split(' ')

        hiddenfields = 'timestamp eth_type eth_dest eth_src ip_tos ip_ttl ip_header_checksum'.split(' ')

        if hidefields and spacket['eth_type'] == '(not IPv4)':
            return

        for field in fields:
            try:
                if spacket.has_key(field) and not (hidefields and field in hiddenfields):            
                    if field == 'ip_payload_data':
                        s += field + ": " + str(spacket[field]).encode("string_escape") + "\n"
                    else:
                        s += field + ": " + str(spacket[field]) + "\n"
            except KeyError:
                pass

        return s

    def pd_ntohs(self, packet, offset):
        return 256*ord(packet[offset])+ord(packet[offset+1])

    def pd_ntohl(self, packet, offset):
        return long(256*256*256*ord(packet[offset])+256*256*ord(packet[offset+1])+256*ord(packet[offset+2])+ord(packet[offset+3]))

    def parse_and_save(self, dump_packet, ignore_tcp_checksum = 1):
        '''
        Parse a pcap file and return a dictionary
        '''

        spacket = {}
        spacket['timestamp'] = "%d.%06d" % (dump_packet[0].getts()[0], dump_packet[0].getts()[1])

        packet = dump_packet[1]
        if ( ord(packet[12]) == 8 and ord(packet[13]) == 0 ): # normal IPv4
            spacket['eth_type'] = "%02x%02x" % (ord(packet[12]), ord(packet[13]))
            ip_packet = packet[14:]
        elif ( ord(packet[12]) == 129 and ord(packet[13]) == 0 ):  # vlan
            if ( ord(packet[16]) == 8 and ord(packet[17]) == 0 ): # normal IPv4, inside vlan
                spacket['eth_type'] = "%02x%02x" % (ord(packet[16]), ord(packet[17]))
                ip_packet = packet[18:]
            else: # not IPv4, in vlan
                spacket['eth_type'] = '(not IPv4)'
                return spacket
        else: # not IPv4, no vlan
            spacket['eth_type'] = '(not IPv4)'
            return spacket

        spacket['eth_dest'] = binascii.hexlify(packet[0:6])
        spacket['eth_src'] = binascii.hexlify(packet[6:12])

        spacket['ip_version'] = binascii.hexlify(ip_packet[0])[0]
        if spacket['ip_version'] != '4':
            spacket['eth_type'] = '(not IPv4)'
            return spacket

        #A few lines of code to make the output easier to read.    
        ip_up_protocol = ord(ip_packet[9])
        ip_up_protocol_int = int(ip_up_protocol)        
        spacket_ip_flags = binascii.hexlify(ip_packet[6:7])    
        spacket_ip_flags_int = int(spacket_ip_flags)
        
        spacket['ip_header_length'] = binascii.hexlify(ip_packet[0])[1]
        spacket['ip_tos'] = binascii.hexlify(ip_packet[1])
        spacket['ip_total_length'] = self.pd_ntohs(ip_packet, 2)
        spacket['ip_ident'] = self.pd_ntohs(ip_packet, 4)


        try:spacket['ip_flags'] = "%s (%s)" % (spacket_ip_flags, tcp_flags[spacket_ip_flags_int] )    
        except:spacket['ip_flags'] = binascii.hexlify(ip_packet[6:7])
        spacket['ip_ttl'] = ord(ip_packet[8])
        #spacket['ip_protocol'] = ord(ip_packet[9])
        spacket['ip_protocol'] = "%s (%s)" % (ip_up_protocol, protocol[ip_up_protocol_int] )        
        spacket['ip_header_checksum'] = binascii.hexlify(ip_packet[10:12])
        spacket['ip_src'] = "%d.%d.%d.%d" % tuple(map(ord,(ip_packet[12:16])))
        spacket['ip_dest'] = "%d.%d.%d.%d" % tuple(map(ord,(ip_packet[16:20])))
        header_len = 4*(ord(ip_packet[0]) & 0xF) # in bytes
        spacket['ip_options'] = binascii.hexlify(ip_packet[20:header_len])
        #payload = ip_packet[header_len:] # also in bytes
        if self.ignore_tcp_checksum and spacket['ip_protocol'] == 6:
            #ignore TCP checksums because of offloading
            payload = ip_packet[header_len:header_len+16] +\
                '\0\0' + ip_packet[header_len+18:spacket['ip_total_length']] # also in bytes
        elif self.ignore_tcp_checksum and spacket['ip_protocol'] == 0x11:
            #ignore UDP checksums because of offloading
            payload = ip_packet[header_len:header_len+4] +\
                '\0\0' + ip_packet[header_len+6:spacket['ip_total_length']] # also in bytes
        else:
            payload = ip_packet[header_len:spacket['ip_total_length']] # also in bytes

        spacket['ip_payload_length'] = len(payload)
        spacket['ip_payload_data'] = payload

        if spacket['ip_protocol'] == 6 and len(payload) >= 8:
            spacket['tcp_port_pair'] = "%d:%d" % (pd_ntohs(payload, 0), pd_ntohs(payload, 2))
            spacket['tcp_sequence_number'] = pd_ntohl(payload, 4)

        return spacket




###############################################################################
###############################################################################
###############################################################################

    def get_packet(self, a, ignore_ip=0):
        '''
        Gets next valid packet from pcapy reader a.
        Valid means IPv4 and between our two hosts (unless ignore_ip == 1).
        Returns a saved packet in dictionary form, or 0 for EOF.
        '''
        while 1:
            try:
                packet = a.next()

            except pcapy.PcapError:
                return 0
            spacket = self.parse_and_save(packet)
            try:
                if (not ignore_ip) and (not self.is_our_traffic(spacket)):
                    # not traffic between our two hosts, so continue
                    continue
            except KeyError:
                continue
            return spacket
            #print spacket

    def is_our_traffic(self, spacket):
        try:
            if self.debug == "debug":
                dsrc = 'spacket ip_src = ', spacket['ip_src']
                ddest = 'spacket ip_dest = ',spacket['ip_dest']
                dlocal = 'ip_local = ', self.ip_local
                dremote = 'ip_remote = ', self.ip_remote
                self.debugfile.append(dsrc)
                self.debugfile.append("\n")
                self.debugfile.append("\n")
                self.debugfile.append(ddest)
                self.debugfile.append("\n")
                self.debugfile.append("\n")
                self.debugfile.append(dlocal)
                self.debugfile.append(dremote)

            if ((spacket['ip_src'] == self.ip_local or spacket['ip_dest'] == self.ip_local) and\
                (spacket['ip_src'] == self.ip_remote or spacket['ip_dest'] == self.ip_remote)):
                if self.debug == "debug":
                    self.debugfile.append('is_our_traffic = 1')
                    self.debugfile.append("\n")
                    self.debugfile.append("\n")
                    self.debugfile.append("\n")
                    
                return 1
            else: 
                if self.debug == "debug":
                    self.debugfile.append('is_our_traffic = 0')
                    self.debugfile.append("\n")
                    self.debugfile.append("\n")
                    self.debugfile.append("\n")
                return 0

        except:
            self.sspacket = 'exception seen in spacket'
            return 0



    def manifest_packet(self, spacket, file):
        '''
        Takes a saved packet (spacket) and applies it to the manifest.
        You need to specify if this packet came from the local file
        or the remote file by specifying the "file" argument as "local"
        or "remote".  Returns a float of timestamp.
        '''
        s = self.packet_to_string(spacket, 1)
        if file == 'remote':
            if s:
                if spacket['ip_src'] == self.ip_remote:
                    self.total['remote'] += 1
                elif spacket['ip_dest'] == self.ip_remote:
                    self.total['remote_received'] += 1
                try:
                    self.manifest[s] -= 1
                    if self.manifest[s] == 0:
                        del(self.manifest[s])
                except KeyError:
                    self.manifest[s] = -1
        elif file == 'local':
            if s:
                if spacket['ip_src'] == self.ip_local:
                    self.total['local'] += 1
                elif spacket['ip_dest'] == self.ip_local:
                    self.total['local_received'] += 1
                try:
                    self.manifest[s] += 1
                    if self.manifest[s] == 0:
                        del(self.manifest[s])
                    self.total['duplicates'] += 1 # no key error => duplicate packet
                except KeyError: self.manifest[s] = 1
        else: raise "Bad file, should be 'local' or 'remote': " % file
        return float( spacket['timestamp'] )

    #shorthand for timestamp of a spacket
    def tsp(self, sp): return float( sp['timestamp'] )


    def getid(self, p): return self.re_ipid.search(p).groups(1)[0]
    ######################
    ##Here is where the real code starts##
    ######################
    def pcapdiff(self, evt):
        try:
            self.pcap_remote = pcapy.open_offline(self.pcap_file2)
        except:
            self.rtxtctrl.WriteText("Error opening file. Please ensure the packet capture is in .pcap format")
            self.rtxtctrl.Newline()
        try:
            self.pcap_local = pcapy.open_offline(self.pcap_file)
        except:
            self.rtxtctrl.WriteText("Error opening file. Please ensure the packet capture is in .pcap format")
            self.rtxtctrl.Newline()
        local_packets = list()
        remote_packets = list()
        local_tpackets = list()
        remote_tpackets = list()
        missingpaks = list()
        tdata = list()
        yes_out_of_sync = 0
        zero_pak_error = 0
        self.rtxtctrl.WriteText(   "Source File: %s\n" %(self.pcap_file))
        self.rtxtctrl.WriteText(   "Destination File: %s\n" %(self.pcap_file2))
        self.rtxtctrl.WriteText(   "Analyzing traffic between % s and %s\n" %(self.ip_local.strip(), self.ip_remote.strip()))
        if self.Time_tpcat == "yes":
                self.rtxtctrl.Newline()
                StartTimeTimestamp = time.strftime("%H:%M:%S",time.localtime())
                self.rtxtctrl.WriteText("Start Time %s"%(StartTimeTimestamp))
                self.rtxtctrl.Newline()        
        self.rtxtctrl.Newline()
        self.rtxtctrl.Newline()
        self.rtxtctrl.Newline()

        next = {}
        next['local']  = self.get_packet(self.pcap_local, 1)  #1 means ignore ip addresses
        next['remote'] = self.get_packet(self.pcap_remote, 1)







            
#########################
#####Remote PACKET CAPTURE######
#########################
        if self.Time_tpcat == "yes":
                self.rtxtctrl.Newline()
                RemoteTimestamp = time.strftime("%H:%M:%S",time.localtime())
                self.rtxtctrl.WriteText("Starting the processing Remote capture")
                
        
        
        while next['remote'] != 0: 
            if next['remote'] == 0:
                break
            next['remote'] = self.get_packet(self.pcap_remote)
            if self.debug == 'debug':
                
                try:dpak = 'next[remote] = ', next['remote']  #print the whole packet
                except: dpak = "couldn't print the whole packet"
                self.debugfile.append(dpak)
                self.debugfile.append("\n")
                self.debugfile.append("\n")
                self.debugfile.append("\n")
            try: #If the header matches the part we are interested in.  
                if next['remote']['ip_src'] == self.ip_local and next['remote']['ip_dest'] == self.ip_remote or next['remote']['ip_src'] == self.ip_remote and next['remote']['ip_dest'] == self.ip_local:
                    try:
                        datapacket2 = next['remote']['ip_src'], next['remote']['ip_dest'], next['remote']['ip_ident']
                        if self.debug == 'debug':
                            drpak  = "Data Packet Remote : ", datapacket2
                            self.debugfile.append(drpak)
                            self.debugfile.append("\n")
                            self.debugfile.append("\n")
                        remote_packets.append(datapacket2)
                    except: pass

                    
                    
                    
                    if self.ignore_timestamps == 1: #This portion is if you want to check latency. The clocks must be correct or it will cause issues.
                        try: 
                            timepacket2 = next['remote']['ip_src'], next['remote']['ip_dest'], next['remote']['ip_ident'], next['remote']['timestamp'],next['remote']['ip_flags']
                            remote_tpackets.append(timepacket2) #and we add it to our packet list
                            if self.debug == 'debug':
                                dtrpak =  "Data tPacket remote: ", timepacket2
                                self.debugfile.append(dtrpak)
                                self.debugfile.append("\n")
                                self.debugfile.append("\n")
                        except: pass
            except:pass
        if self.Time_tpcat == "yes":            
            #self.rtxtctrl.WriteText("Completed Remote Capture")
            self.rtxtctrl.Newline()
            RemoteTimestamp2 = time.strftime("%H:%M:%S",time.localtime())
            #self.rtxtctrl.WriteText(RemoteTimestamp2)
            #self.rtxtctrl.Newline()
            edited_RemoteTimestamp= RemoteTimestamp.replace(":","")
            edited_RemoteTimestamp2= RemoteTimestamp2.replace(":","")
            delta = (int(edited_RemoteTimestamp2)-int(edited_RemoteTimestamp))
            self.rtxtctrl.WriteText("Completed Remote Capture - Process Time: %s"%(str(delta)))
            #self.rtxtctrl.WriteText(str(delta))
            self.rtxtctrl.Newline()
            self.rtxtctrl.Newline()
        
#########################
###//Remote PACKET CAPTURE//######
#########################









        
#########################
#####LOCAL PACKET CAPTURE######
#########################
        if self.Time_tpcat == "yes":
                self.rtxtctrl.WriteText("Starting the processing Local capture")
                LocalTimestamp = time.strftime("%H:%M:%S",time.localtime())
                #self.rtxtctrl.WriteText(LocalTimestamp)
                
        while next['local'] !=  0: #Look through every packet in the local file. We get a 0 if there is no more pacekts to go through.
            next['local'] = self.get_packet(self.pcap_local, 1) #We now open up the next packet
            if next['local'] == 0:
                break
            if self.debug == 'debug':                
                try:dpak = 'next[local] = ', next['local']  #print the whole packet
                except: dpak = "couldn't print the whole packet"
                self.debugfile.append(dpak)
                self.debugfile.append("\n")
                self.debugfile.append("\n")
                self.debugfile.append("\n")
            if self.ignore_timestamps == 1: #This portion is if you want to check latency. The clocks must be correct or it will cause issues.
                    try: #Here we build our datapak 
                        timepacket = next['local']['ip_src'], next['local']['ip_dest'], next['local']['ip_ident'], next['local']['timestamp'],next['local']['ip_flags']
                        local_tpackets.append(timepacket) #and we add it to our packet list
                        if self.debug == 'debug':
                            dltpak = "Data tPacket Local: ", timepacket
                            self.debugfile.append(dltpak)
                            self.debugfile.append("\n")
                            self.debugfile.append("\n")
                            self.debugfile.append("\n")                            
                            
                    except:pass

            try:
                if next['local']['ip_src'] == self.ip_local and next['local']['ip_dest'] == self.ip_remote or next['local']['ip_src'] == self.ip_remote and next['local']['ip_dest'] == self.ip_local:
                    datapacket = next['local']['ip_src'], next['local']['ip_dest'], next['local']['ip_ident']
                    local_packets.append(datapacket) #and we add it to our packet list
            except: pass
#################################
#################################
#################################
#################################

        if self.Time_tpcat == "yes":            
            #self.rtxtctrl.WriteText("Completed Local Capture")
            LocalTimestamp2 = time.strftime("%H:%M:%S",time.localtime())
            #self.rtxtctrl.WriteText(LocalTimestamp2)
            self.rtxtctrl.Newline()
            edited_LocalTimestamp= LocalTimestamp.replace(":","")
            edited_LocalTimestamp2= LocalTimestamp2.replace(":","")
            delta = (int(edited_LocalTimestamp2)-int(edited_LocalTimestamp))
            self.rtxtctrl.WriteText("Completed Local Capture - Process Time: %s"%(str(delta)))
            #self.rtxtctrl.WriteText(str(delta))
            self.rtxtctrl.Newline()
            self.rtxtctrl.Newline()

            
            #A dummy check for Matt. If either side reports 0 matching packets Error out. It's pretty pointless to continue. 
        if len(local_packets) == 0 or len(remote_packets) == 0:
            zero_pak_error = 1
            self.rtxtctrl.WriteText("ERROR: %s packets matched on local side and %s packets matched on remote side. Please check your IP filters"%(len(local_packets), len(remote_packets)))
            self.rtxtctrl.Newline()
            self.rtxtctrl.Newline()
            
        #Here we sync the two packet captures. Basically Take a look at the two captures and find the first matching packet. Then we analyze the data using that as our starting point.
        #This will *hopefully* weed out false positives in regards to the captures being started at slightly different times
        if self.out_of_sync ==1:
            for syncpak in local_packets: 
                if not syncpak in remote_packets:
                    dsypak = syncpak, "was not found on the remote side"
                    self.debugfile.append(dsypak)
                    self.debugfile.append("\n")
                    missingpaks.append(syncpak)
                    yes_out_of_sync = 1
                if syncpak in remote_packets:
                    dspak = "starting packet is", syncpak
                    self.debugfile.append(dspak)
                    break
                
                
        
        if self.Time_tpcat == "yes":
                self.rtxtctrl.WriteText("Analyzing the two packet captures...")
                self.rtxtctrl.Newline()
                Local_to_RemoteTimestamp = time.strftime("%H:%M:%S",time.localtime())
                #self.rtxtctrl.WriteText(Local_to_RemoteTimestamp)
                self.rtxtctrl.Newline()

         #Using set, we're going to put it in a format set understands..
        setted_local_packets = set(local_packets)
        setted_remote_packets = set(remote_packets)
        if self.debug == "debug":
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("LOCAL PACKET LIST:")
            self.debugfile.append(setted_local_packets)
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("\n")
            self.debugfile.append("REMOTE PACKET LIST:")
            self.debugfile.append(setted_remote_packets)
            
            
            #if the packet captures appear out of sync
        total_mpaks = 0
        if yes_out_of_sync ==1:
            self.rtxtctrl.WriteText("-Warning, packet captures appear out of sync. Cleaning things up for you..-")
            self.rtxtctrl.Newline()
            for mpak in missingpaks:
            	dmpak = "missing packet", mpak
                self.debugfile.append(dmpak)
                self.debugfile.append("\n")
                setted_local_packets.discard(mpak)
                total_mpaks = total_mpaks+1
            self.rtxtctrl.WriteText("Removed %s packets to sync the two captures"%(total_mpaks))
            self.rtxtctrl.Newline()
        #Do a quick check, do these two already match? 
        stare_and_compare = setted_local_packets <= setted_remote_packets
        
        
        if stare_and_compare == True and zero_pak_error == 0:
            self.rtxtctrl.WriteText("Packet Captures Match. Terminating..Man that was easy!")
            self.rtxtctrl.Newline()
            self.rtxtctrl.Newline()
            self.rtxtctrl.Newline()
        else:
            differences = setted_local_packets ^ setted_remote_packets
            
            for datapak in differences:
                if not datapak in remote_packets:

                    src,dst,ipid = datapak 
                    self.rtxtctrl.BeginBold()
                    self.rtxtctrl.WriteText(   "Packet Dropped - Source:")
                    self.rtxtctrl.EndBold()
                    self.rtxtctrl.WriteText(   " %s "%(src))
                    self.rtxtctrl.BeginBold()
                    self.rtxtctrl.WriteText(   " Destination: ")
                    self.rtxtctrl.EndBold()
                    self.rtxtctrl.WriteText(   " %s "%(dst))
                    self.rtxtctrl.BeginBold()
                    self.rtxtctrl.WriteText(   " IPID: ")
                    self.rtxtctrl.EndBold()
                    self.rtxtctrl.WriteText(   " %s "%(ipid))
                    self.rtxtctrl.Newline()

            
                if not datapak in local_packets:

                    src,dst,ipid = datapak 
                    self.rtxtctrl.BeginBold()
                    self.rtxtctrl.WriteText(   "Packet Forged - Source:")
                    self.rtxtctrl.EndBold()
                    self.rtxtctrl.WriteText(   " %s "%(src))
                    self.rtxtctrl.BeginBold()
                    self.rtxtctrl.WriteText(   " Destination: ")
                    self.rtxtctrl.EndBold()
                    self.rtxtctrl.WriteText(   " %s "%(dst))
                    self.rtxtctrl.BeginBold()
                    self.rtxtctrl.WriteText(   " IPID: ")
                    self.rtxtctrl.EndBold()
                    self.rtxtctrl.WriteText(   " %s "%(ipid))
                    self.rtxtctrl.Newline()

        if self.Time_tpcat == "yes":            
           
            Local_to_RemoteTimestamp2 = time.strftime("%H:%M:%S",time.localtime())
            #self.rtxtctrl.WriteText(LocalTimestamp2)
            #self.rtxtctrl.Newline()
            edited_Local_to_RemoteTimestamp= Local_to_RemoteTimestamp.replace(":","")
            edited_Local_to_RemoteTimestamp2= Local_to_RemoteTimestamp2.replace(":","")
            delta = (int(edited_Local_to_RemoteTimestamp2)-int(edited_Local_to_RemoteTimestamp))
            self.rtxtctrl.WriteText("Completed Analyzing of all packets - Process Time: %s"%(str(delta)))
#################################
#################################
#################################
#################################
#################################

        #Kinda ugly, but it works..
        if self.ignore_timestamps == 1:
            self.rtxtctrl.Newline()
            self.rtxtctrl.Newline()
            self.rtxtctrl.WriteText("Calculating latency between the two packet captures:")
            self.rtxtctrl.Newline()
            self.rtxtctrl.Newline()
            for l_tdatapak in local_tpackets: #For each data packet in the local packet capture
                ip_src,ip_dest,ipid,timestamp,ip_flags = l_tdatapak #unpack the data to search for the ipheader
                l_ipheader = (ip_src, ip_dest,ipid,ip_flags) #Rebuild the packet
                #print l_ipheader
                #x = l_ipheader in remote_tpackets
                #print x
                #if ipheader in remote_packets: #Search the remote side. Did it come through? If it did, lets compare timestamps
                for r_tdatapak in remote_tpackets:
                    ip_src,ip_dest,ipid,timestamp,ip_flags = r_tdatapak #unpack the data to search for the ipheader
                    r_ipheader = (ip_src, ip_dest, ipid,ip_flags)
                    if r_ipheader == l_ipheader:
                        #print "Match found - ", r_ipheader, l_ipheader
                        src,dst,ipid,timestamp,ip_flags = l_tdatapak 
                        rsrc,rdst,ripid,rtimestamp,rip_flags = r_tdatapak 
                        tdelta = float(rtimestamp) - float(timestamp)
                        tdata.append(tdelta)
                        #self.rtxtctrl.WriteText(   "IPID: %s Packet Type: %s Time Delta(Latency): %s \n" %(ipid,ip_flags, tdelta))
                        self.rtxtctrl.BeginBold()
                        self.rtxtctrl.WriteText(   "IPID:")
                        self.rtxtctrl.EndBold()
                        self.rtxtctrl.WriteText(   " %s "%(ipid))

                        self.rtxtctrl.BeginBold()
                        self.rtxtctrl.WriteText(   "Packet Type:")
                        self.rtxtctrl.EndBold()
                        self.rtxtctrl.WriteText(   " %s "%(ip_flags))

                        self.rtxtctrl.BeginBold()
                        self.rtxtctrl.WriteText(   "Time Delta (Latency):")
                        self.rtxtctrl.EndBold()
                        self.rtxtctrl.WriteText(   " %s "%(tdelta))
                        self.rtxtctrl.Newline()
                        #self.rtxtctrl.WriteText(   "Source:%s   Destination:%s    IPID: %s TimeStamp: %s \n" %(rsrc,rdst,ripid, rtimestamp))
                #if self.debug == 'debug':
                    #print tdatapak, "Was found"

                    
                    
        if self.ignore_timestamps == 1:
            self.rtxtctrl.Newline()
            total_tdata = sum(tdata) 
            num_tdata = len(tdata)
            avg_tdata = total_tdata/num_tdata 
            hi_tdata = max(tdata)
            lo_tdata = min(tdata)
            self.rtxtctrl.BeginBold()
            self.rtxtctrl.WriteText(   "Average Latency Seen:")
            self.rtxtctrl.EndBold()
            self.rtxtctrl.WriteText(   " %s \n"%(tdelta))
            self.rtxtctrl.BeginBold()
            self.rtxtctrl.WriteText(   "Max Latency Seen:")
            self.rtxtctrl.EndBold()
            self.rtxtctrl.WriteText(   " %s \n"%(hi_tdata))
            self.rtxtctrl.BeginBold()
            self.rtxtctrl.WriteText(   "Min Latency Seen:")
            self.rtxtctrl.EndBold()
            self.rtxtctrl.WriteText(   " %s \n"%(lo_tdata))
            self.rtxtctrl.Newline()
            self.rtxtctrl.Newline()

        if self.Time_tpcat == "yes":            
           
            EndTimeTimestamp = time.strftime("%H:%M:%S",time.localtime())
            #self.rtxtctrl.WriteText(LocalTimestamp2)
            self.rtxtctrl.Newline()
            self.rtxtctrl.Newline()
            edited_EndTimeTimestamp= EndTimeTimestamp.replace(":","")
            edited_StartTimeTimestamp= StartTimeTimestamp.replace(":","")
            delta = (int(edited_EndTimeTimestamp)-int(edited_StartTimeTimestamp))
            self.rtxtctrl.WriteText("Total Process Time: %s"%(str(delta)))

        
        self.rtxtctrl.Newline()
        self.rtxtctrl.Newline()                    
        self.rtxtctrl.WriteText(   "Number of Packets in the Source Capture : %s\n" %(len(local_packets)))
        self.rtxtctrl.WriteText(   "Number of Packets in the Destination Capture : %s\n" %(len(remote_packets))) 
                
                
        if self.debug == "debug":
            dlg = wx.FileDialog(
                self, message="Save file as ...", defaultDir=os.getcwd(), 
                defaultFile="", wildcard=wildcard2, style=wx.SAVE
                )

            dlg.SetFilterIndex(2)
            sfile = self.rtxtctrl.GetValue()
            if dlg.ShowModal() == wx.ID_OK:
                path = dlg.GetPath()
                fp = file(path, 'w') # Create file anew
                fp.write(sfile)
                for dline in self.debugfile:
                    #print str(dline)
                    fp.write(str(dline))
                fp.close()

            dlg.Destroy()



        
                
class MyApp(wx.App):
    def OnInit(self):
        frame = MyFrame(None, "TPCAT")
        #self.SetTopWindow(frame)
        frame.SetToolTip(wx.ToolTip(''))
        frame.SetPosition(wx.Point(50,50))
        frame.SetIcon(wx.Icon('firewall.ico', wx.BITMAP_TYPE_ICO))
        frame.SetSize(wx.Size(595,700))
        frame.SetTitle('                                                                                   -TPCAT-')
        frame.Show(True)
        return True


app = MyApp(redirect=True)
app.MainLoop()






############################TO DO############################
#Add option for CVS format
#
############################################################


############Known issues########################
#If you encounter the error below you will need to install winpcap. This comes bundled with wireshark or you can download it manually.
#
"""
Traceback (most recent call last):
  File "TPCAT.pyw", line 12, in <module>
  File "zipextimporter.pyc", line 91, in load_module
ImportError: MemoryLoadLibrary failed loading pcapy.pyd
"""
#
###########################################

#######Change log##############
#06/06/2009- Version 2.2 Greatly improved the debug feature. Added a few minor features to improve things and added the ability to record how long tpcat takes. 
#06/07/2009- Version 2.1 Fixed the matt bug with the check boxes. Added the capture sync option and a couple of dummy checks
#06/06/2009- Version 2.0 Updated the core code of the analyzing engine. Speed improvements are huge when using files over a couple of meg
#11/24/2008 - Version 1.3 fixed several bugs found by my  peers with the GUI. Also made the options more straight forward. Added different levels of verbosity. 
#                                       Added latency Average/Min/Max
#11/24/2008 - Version 1.2 Added latency calculation and forged packet awareness. 
#11/23/2008 - Version 1.1 Fixed a few issues with reporting and false positives
#11/22/2008 - Version 1.0 Re-wrote the pcapdiff back end, or at least a large part of it. What was there just wasn't working for me. This way I have something from the ground up.
#11/20/2008 - Version 0.7 Fixed a bug with the timestamps. It was set to the wrong default causing false positives.
#11/20/2008 - Version 0.6 TPCAT is now working and can do base comparisons. . All bugs resolved that I am aware of. I need to go back and add some additional features such as:
#			ignore clock, verbosity, ignore checksums..etc. These features exists in pcapdiff they might as well be here.
#11/15/2008 - Version 0.5 Fixed a few bugs with my modules, fixed the bug that caused the same file to be loaded as local and remote. Small typo = major problem
#11/10/2008 - Version 0.4 improvements to GUI made. Also fixed a bug with it crashing upon loading files
# 11/7/2008 - Version 0.3 Pcapdiff code has lots of issues. Mostly with calling vairbles since we're not working out of a class. Fixed a majority of them.
# 11/6/2008 - Version 0.2 Pcapdiff code added and smashed. 
# 11/5/2008 - Version 0.1 Base GUI built. Starting to port over pcapdiff code
############################

##Raw Packet dump output for reference:###
"""
next[local] =  {'eth_dest': '0010dbff6090', 'ip_dest': '10.13.120.7', 'ip_protocol': '6 (TCP )', 'ip_options': '', 'ip_header_length': '5', 'timestamp': '1227110191.201274', 'ip_ident': 19530, 'ip_payload_length': 50, 'ip_flags': '40 (reset)', 'ip_ttl': 64, 'eth_type': '0800', 'ip_payload_data': '\x83\x17\x01\x85U\x1e\x8a\x8a\xd1\xd70\x1fP\x18\x83,\xb0\x14\x00\x000\x1c\x02\x01\x01`\x17\x02\x01\x03\x04\tcn=4guser\x80\x07sdfrun1', 'ip_header_checksum': '6240', 'ip_version': '4', 'eth_src': '00144f7cc328', 'ip_tos': '00', 'ip_total_length': 70, 'ip_src': '10.207.255.68'}
"""
