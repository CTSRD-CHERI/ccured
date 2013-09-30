// -*- Mode: java -*-
/*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

/* This file is read by the CCured application and spliced into the emitted 
 * html. While doing this tags of the form @@xxxxx@@ are replaced 
 * with customized values */

/* The names of the functions that are used in server-code are kept short to 
 * reduce the size of the html file */

sourceFrame = "sourcecode";      	// frame containing infer file
graphInfoFrame = "nodeinfo";		// frame to write graph info into
formFrame = "form";
codeFrameCode = "parent"; // The code to obtain the frame that
                          // contains this code
dataFrame = 'data';

// See if we are in IE
var isIE = navigator.appName == "Microsoft Internet Explorer";

var debugSchedule = false;

var logWindow;

// The list of nodes. Will initialize from code
var nodelist;

// How many nodes do we have in a file
var nodesPerFile;

// For each node file, remember if we have loaded it
var nodeFileLoaded = new Array(128);


// The list of edges. Will initialize from code
var edgelist;

// How many edges do we have in a file
var edgesPerFile;

// For each edge file, remember if we have loaded it
var edgeFileLoaded = new Array(128);

// The bad casts (array of indices)
var nrBadCasts = 0;
var badCastEdge;
var badCastIsSeq;

// The arrays that store the globals and the types (sorted)
var globalslist;
var typeslist;

// The incompatible classes
var nrIncompat = 0;
// An array containing "src:n1@e1,...,nk@ek" data for each incompatibility
var incompatClass;

// The array containing the fileIdx:featureIdx for forward features
// Will be initialized from the form file.
var forwardFeatures;

// Here we'll load the encoding of kinds using code from server
var kindCodes = new Array(32);

// Here we'll load then filename codes using code from server
var fileCodes = new Array(32);

// Here we'll load the flag codes using code from server
var flagCodes = new Array(32);
  
// The basehref. Drop the index.html from the end of this file
var basehref = findBasehref(window.location.href);

// Save here the current node shown
var currentNodeShown;

var pixel = new Image();
pixel.src= "pixel.gif";
var bullet = new Image();
bullet.src= "bullet.gif";


// Store here theimage that was turned into a bullet
var imageMadeBullet = undefined;

var loadedFragment = 0; // The index of the currently loaded fragment

/* 
*	Node Constructor
*	creates a new Node object
*	represents a node in the infer graph
*/
function Node(nodeNumber, // The number of the node
              kind // The kind
              ) {
    this.nodeNumber = nodeNumber;
    this.kind = kind;
}


/* Edge constructor */
function Edge(edgeIdx, nodeFrom, nodeTo, edgeKind, eFile, eLine) {
  this.idx   = edgeIdx;
  this.from  = nodeFrom;
  this.to    = nodeTo;
  this.ekind = edgeKind;
  this.efile = eFile;
  this.eline = eLine;
}


// Add a global
function ag(idx,data) {
    globalslist[idx] = data;
}
// Add a type
function at(idx,data) {
    typeslist[idx] = data;
}

/* 
*	NodeList::AddNode
*	adds node with the supplied parameters to NodeList 
*/
function an(num,fileIdx,kind,why_kind) {
    var n = new Node(num,kind);
    n.whykind = why_kind;

    // See if we have some additional arguments
    if(an.arguments.length > 4) {
        n.whyArray = new Array(an.arguments.length - 4);
        for(var i=4;i<an.arguments.length;i++) {
            n.whyArray[i-4]=an.arguments[i];
        }
    }
    // JavaScript re-assigns array length automatically
    if(fileIdx >= 0) {
        // Leave the fileIdx undefined if the node is not marked-up
        n.fileIdx  = fileIdx;
    }
    nodelist[num] = n;  
}


// Add node flags. This is a vararg function where the first
// argument is the node number, the second is a flag index
// and the rest are an encoding of the flag
function nf(num, fidx) {
    var n = nodelist[num]; // We know this has just been loaded
    if(n.flags == undefined) { n.flags = new Array(10); }
    n.flags[fidx] = new Array(nf.arguments.length - 2);
    for(var i=2 ; i < nf.arguments.length; i++) {
        n.flags[fidx][i-2] = nf.arguments[i];
    }
}

// Add an edge
function ae(eidx,nfrom,nto,ekind,efile,eline) {
  var e = new Edge(eidx,nfrom,nto,ekind,efile,eline);
  // Some edges have corresponding markers
  if(ae.arguments.length > 6) {
      e.markFileIdx = ae.arguments[6];
      e.markIdx     = ae.arguments[7];
  }
  edgelist[eidx] = e;
}


/*
*	showNode()
*	displays information about node 'node' in frame 'graphInfoFrame',
*	uses 'outputNodeinfo()'
*       This function is called with a node ID (as in markptr)
*/
function sn(node_id, repos) {
    if(nodelist == undefined) {
        alert("The form has not finished loading\n"); return;
    }
    if(node_id < 0 || node_id >= nodelist.length) {
        alert("Invalid node number " + node_id); return;
    }
    entryPoint(function () { showNode(node_id, repos); });
}
function showNode(node_id, repos) {
    var node = loadNodeInfo(node_id);
    if(node == undefined) {
        return;
    }
    currentNodeShown = node;
    showFeature(node.fileIdx, "in" + node.nodeNumber, repos);

    // Now fill in the graphInfo frame
    var f = frames[graphInfoFrame];
    var d = f.document;
    
    outputNodeinfo(d,node);
}


/*
*	showFeature()
*	repositions the point and marks the given feature
*/
function showFeature(fileIdx, featureName, repos) {
    // Now clear the previous mark
    if (imageMadeBullet != undefined) {
        imageMadeBullet.src = pixel.src;
    }
    if(fileIdx == undefined) {
        // There is no markup for this one. Return now after we have cleared
        // the marker
        return;
    }
    // Make sure we have the right file loaded
    loadSourceFileFragment(fileIdx);
    // Actually while failedBecauseWaitingForFile is set we do not
    // know for sure that we finished loading the source file
    
    var sFrame = frames[sourceFrame];
    var sDoc = sFrame.document;
    // Find the image for the feature
    // This is according to the documentation
    imageMadeBullet = sDoc.images[featureName];
    if(imageMadeBullet == undefined && sDoc.all != undefined) {
        // This seems to work in IE
        imageMadeBullet = sDoc.all[featureName];
        // If the result is an array then pick the first element
        if(imageMadeBullet != undefined && imageMadeBullet[0] != undefined) {
            imageMadeBullet = imageMadeBullet[0];
        }
    }
    if(imageMadeBullet == undefined || imageMadeBullet.src == undefined) {
      // See if we still have files to be loaded
      if(! failedBecauseWaitingForFile) {
        alert("Cannot find feature " + featureName + ".");
        return;
      }
      // Otherwise we know we'll retry this
      imageMadeBullet = undefined;
      return;
    }
    // Mark the node with a bullet
    imageMadeBullet.src=bullet.src;
    if(repos) {
        // Scroll a bit

        // Find the height of the frame
        var frameHeight = sFrame.innerHeight; // Works in Navigator;
        var frameWidth  = sFrame.innerWidth;
        if(frameHeight == undefined &&
           sFrame.frameElement &&
           sFrame.frameElement.height != undefined) {
            frameHeight = sFrame.frameElement.height; // Works in IE
            frameWidth = sFrame.frameElement.width;
        }
        if(frameHeight == undefined) {
            alert("Cannot find the frameHeight");
            return;
        }
        // Find the position of the image
        var imageY, imageX, doScroll = true;
        if(imageMadeBullet.offsetTop != undefined) { 
            // Works in IE
            imageY = imageMadeBullet.offsetTop;
            imageX = imageMadeBullet.offsetLeft;
            doScroll = true;
        } else {
            // I do not know how to get the coordinates of the image on Navig.
            /* I am relying on the fact that we also have anchors for all 
             * features. The name of the feature is "i" + anchorName */
            var anchorName = featureName.substr(1);
            var imageY = sFrame.pageYOffset; // Get the old position
            sFrame.location.hash = anchorName;
            // Wait until it has been scrolled, or 1s
            // for(var i=0;imageY == sFrame.pageYOffset && i < 100000;i++) { }
            // alert("imageY = "+imageY+" now= "+sFrame.pageYOffset);
            // Now we can get the approximate position of the image
            imageY = sFrame.pageYOffset;
            imageX = sFrame.pageXOffset;
            doScroll = false; // Not reliable
        }
        var toScrollY = imageY - frameHeight / 2;
        if(toScrollY < 0) toScrollY = 0;
        var toScrollX = imageX - frameWidth / 2;
        if(toScrollX < 0) toScrollX = 0;
        // alert("imageX="+imageX+" imageY="+imageY+" frameHeight="+frameHeight);
        if(doScroll) {
            sFrame.scrollTo(toScrollX, toScrollY);
        }
    }
}

// An entry point for showing a feature
function sf(fileIdx, featureName) {
  entryPoint(function () { showFeature(fileIdx, featureName, 1); });
}


// An entry pointer for showing a forward feature
function sff(forwardFeatureId) {
  if(forwardFeatureId < 0 || forwardFeatureId >= forwardFeatures.length) {
    alert("Invalid forward feature index: "+forwardFeatureId);
    return;
  }
  // Fetch the information about the forward feature
  var forwardData = forwardFeatures[forwardFeatureId];
  // Split it as fileIdx:featureIdx
  var idx = forwardData.indexOf(':');
  if(idx <= 0) {
    alert("Forward feature data "+forwardData+" does not contain a ':'");
    return;
  }
  var fileIdx = forwardData.substr(0,idx) - 0;
  var featureName = "if" + forwardData.substr(idx+1);
  if(fileIdx < 0) {
    alert("Cannot find the definition of this feature");
    return;
  }
  sf(fileIdx, featureName);
}

/******* DECODER *************/
// Decoding of locations
function decodeLocation(file, line, featureFileIdx, featureIdx) {
    var res = fileCodes[file] + ':' + line;
    if(featureFileIdx != undefined) {
        return "<a href=\"javascript:" + codeFrameCode + ".sf("
            + featureFileIdx + ", 'if" + featureIdx + "');\">"
            + res +"</a>";
        
    } else {
        return res;
    }
}

// Printing of nodes in the node info frame
function printNode(num) {
    if(num == undefined) { return "loading";  }
    return "<a href=\"javascript:" + codeFrameCode + ".sn(" + num + ", 1);\">"
        + num +"</a>";
}


/* Decode an edge. Use when you know for sure that this is exactly a single 
 * edge (and not an ECompat edge, which also encodes a reason). Use 
 * decodeEdge otherwise */
function decodeOneEdge(eidx) {
    // An actual edge
    if(eidx < 0) { // Most likely you called this function on a ECompat edge
        alert("Called decodeOneEdge("+eidx+")"); return undefined;
    }
    var e = loadEdgeInfo(eidx);
    if(e == undefined) { return ("(loading edge " + eidx + ")"); }
    switch(e.ekind) {
    case 0: k = 'cast'; break;
    case 1: k = 'union field compatibility'; break;
    case 2: k = 'mkptr constraint'; break;
    case 3: k = 'copytags constraint'; break;
    case 4: k = 'method override'; break;
    case 5: k = 'extends pragma'; break;
    case 6: k = 'auto rtti inference'; break;
    case 10: k = 'trusted cast'; break;
    case 11: k = 'eindex'; break;
    case 12: k = 'esafe'; break;
    case 13: k = 'epoints'; break;
    case 14: k = 'eargs'; break;    
    case 15: k = 'esametype'; break;    
    case 16: k = 'tagged union fields have the same kind'; break;    
    default: alert('Unexpected edge kind ' + e.ekind);
    }
    return k + " (" + printNode(e.from) + "->" + printNode(e.to) 
        + ") at " + decodeLocation(e.efile, e.eline,
                                   e.markFileIdx, e.markIdx);
}

// Decode an edge (or a list of edges)
function decodeEdge(d, array, idx, inlist) {
    var eidx = array[idx];
    if(eidx == undefined) {
        alert("decodeEdge(idx="+idx+") but array[idx] is undefined");
        return;
    }
    if(eidx > 0) {
        if(inlist) d.writeln("<LI>");
        d.writeln(decodeOneEdge(eidx));
    } else {
        decodeReason(d, array, idx, inlist);
    }
}

// Decode a reason
function decodeReason(d, array, idx, inlist) {
    var len = array[idx];
    if(len == undefined) {
        alert("decodeReason(idx="+idx+") but array[idx] is undefined");
        return;
    }
    len = - len; // Reasons always have negated length to distinguish from edges
    var startList = (len > 1) && !inlist;
    if(startList) d.writeln("<UL>");

    for(var i=0;i<len;i++) {
        var edgeidx = array[idx + 1 + i];
        if(edgeidx < 0) { edgeidx = - edgeidx; } // Ignore RSym for now
        if(inlist || startList) d.writeln("<LI>");
        d.writeln(decodeOneEdge(edgeidx));
    }
    if(startList) d.writeln("</UL>");
}
   

// Decoding of why_kind
function decodeWhyKind(d, node, inlist) {
  var mainCode = node.whykind & 0x0F;
  var extraInfo = node.whykind >> 4;
  if(inlist) d.writeln("<LI>");
  switch(mainCode) {
  case 0: d.writeln('unconstrained'); return;
  case 1: d.writeln('user specified'); return;
  case 2: d.writeln('void* equivalent to scalar'); return;
  case 3: d.writeln('default'); return;
  case 4: d.writeln('printf argument'); return;
  case 5:
      d.writeln(flagCodes[extraInfo] + " : ");
      decodeWhyFlag(d, node, extraInfo, inlist);
      return;
  case 6: d.writeln('unsafe union'); return;
  case 7:
      d.writeln('special at '
                + decodeLocation(node.whyArray[0], node.whyArray[1]));
      return;
  case 8:
      // This is a bad edge but maybe it should be reported as
      // heterogeneous class
      if(node.whyArray[1] == undefined) {
          d.writeln('bad ' + decodeOneEdge(node.whyArray[0]));
      } else {
          d.writeln('incompatible types for nodes '
                    + printNode (node.whyArray[1])
                    + " and " + printNode (node.whyArray[2]) + " because");
          decodeReason(d, node.whyArray, 3, true);
          d.writeln('<li>WILD propagates here because:');
      }
      return;
  case 9:
      d.writeln('bad (and cannot be sequence) ' +
                decodeOneEdge(node.whyArray[0]));
      return;
  case 10:
      d.writeln('incompatible types for nodes '
                + printNode (extraInfo)
                + " and " + printNode (node.whyArray[0]) + " because");
      decodeReason(d, node.whyArray, 1, true);
      d.writeln('<li>WILD propagates here because:');
      return;
  case 11: // Spread from node
      {
          var n_source_id = extraInfo;
          var n_near_id   = node.whyArray[0];
          // Explain first why the near node has the kind
          var near = loadNodeInfo(n_near_id);
          if(near != undefined) { 
              decodeWhyKind(d, near, inlist);
          }
          // Explain now why this node relates to the near one
          decodeReason(d, node.whyArray, 1, true);
          return;
      }
  default:
    alert('Node ' + node.nodeNumber + ' has invalid whyKind');
  }
}

// Decode flags
function decodeFlags(d, node) {
    var i = 0;
    d.writeln("Flags:<ul>");
    for(var i=0;i<node.flags.length;i++) {
      if(node.flags[i] == undefined) { continue; } // This flag is not set
      // Show only a few flags
      // if(i != 5 && // Reach string
      //   i != 6) continue; // Reach index 
          
      d.write("<li>" + flagCodes[i] + " : ");
      decodeWhyFlag(d, node, i, 0);
    }
    d.writeln("</ul>");
}
// Print the decoding of the given flag
function decodeWhyFlag(d, node, fidx, inlist) {
  var whyArray = node.flags[fidx];
  var flagWhyCode = whyArray[0] & 0x7;
  var flagData    = whyArray[0] >> 3;
  switch(flagWhyCode) {
  case 0: // Spread flag
      var near = whyArray[1];
      var orig = flagData;
      if(! inlist) { // Start a list for this spread
          d.writeln("<ul>");
      }
      // Recursively print the reason for the near node
      var near_n = loadNodeInfo(near);
      // First explain why the near node has the flag
      if(near_n != undefined) {
          decodeWhyFlag(d, near_n, fidx, 1);
      }
      // Now explain why the near node is related to this one
      decodeReason(d, whyArray, 2, true);
      if(! inlist) {
          d.writeln("</ul>");
      }
      break;
    case 1:
      if(inlist) d.write("<li>");
      d.write(" syntax on node " + printNode(node.nodeNumber) +
              " at " + decodeLocation(flagData, whyArray[1], whyArray[2],
                                      whyArray[3]));
      break;
    case 2:
      if(inlist) d.write("<li>");
      d.write(" downcast with node " + printNode(flagData));
      break;
    case 3:
      if(inlist) d.write("<li>");
      d.write(" bad subtype with node " + printNode(flagData));
      break;
      
    case 4:
      if(inlist) d.write("<li>");
      d.write(" required by edge ");
      decodeEdge(d, node, whyArray, 1, 0);
      break;
      
    case 5:
      if(inlist) d.write("<li>");
      d.write(" required by pointer kind " + kindCodes[flagData]
              + " on " + printNode(node.nodeNumber));
      break;
      
    case 6: // Required by flag
      d.write(" " + flagCodes[flagData]);
      break;

    case 7:
      if(inlist) d.write("<li>");
      d.write(" user annotation at " +
              decodeLocation(flagData, whyArray[1], whyArray[2], whyArray[3]));
      break;
      
    default:
      alert("Invalid whyflag code " + flagWhyCode
            + " for node " + node.nodeNumber);
  }
}


/*  
*	outputNodeinfo(d, node)
*	output the information about a node, 
*	in document 'd'
*       This function is called with a node object
*/
function outputNodeinfo(d,node) {
    d.open();
    // set background to white
    if (d.bgColor != "FFFFFF") 
        d.bgColor = "FFFFFF";
    // Write the style
    d.writeln("<link rel=stylesheet type='test/css' href='styles.css'>");
    d.writeln("*** Node " + printNode(node.nodeNumber) + ".<BR>");
    d.writeln("Kind " + kindCodes[node.kind] + " : ");
    decodeWhyKind(d, node, 0);
    d.writeln("<BR>");
    /* Decode the flags. Actually do not. */
    if(node.flags != undefined) { decodeFlags(d, node); }
    d.close();
}



// Show the bad casts
function showBadCast(start) {
    // Create a new window
    if(nrBadCasts == 0) {
        alert("There are no bad casts"); return;
    }
    if(start == undefined) { start = 0; }
    var d = window.open("",
                        "badcasts","width=400,height=250,resizable=1,scrollbars=1").document;
    entryPoint(function () { outputBadCastsOrIncompat(d,
                                                      "Cast",
                                                      nrBadCasts,
                                                      start,
                                                      5, 
                                                      outputOneBadCast); });
}

// Show the incompat classes
function showBadIncompat(start) {
    // Create a new window
    if(nrIncompat == 0) {
        alert("There are no incompatible classes"); return;
    }
    if(start == undefined) { start = 0; }
    var d = window.open("",
                        "badincompat","width=400,height=250,resizable=1,scrollbars=1").document;
    entryPoint(function () { outputBadCastsOrIncompat(d,
                                                      "Incompat", 
                                                      nrIncompat,
                                                      start,
                                                      3,
                                                      outputOneIncompat); });
}


// This function outputs the bad casts
// start is 0 based
function outputBadCastsOrIncompat(d, name, totalCount, start,
                                  toShow, outputOne) {
    d.open();
    var oldCodeFrameCode = codeFrameCode;
    codeFrameCode = "opener";
    var totalThingsToShow = nrBadCasts;
    var last =
        start + toShow < totalCount ?
        start + toShow - 1 : totalCount  - 1;
    d.writeln("Bad "+name+" #"+(start+1)+" to #"+(last+1)+"<BR>");
    if(start > 0) {
        d.writeln("<a href='javascript:opener.showBad"+name+"("+
                  (start - toShow) +
                  ");'>Previous bad "+name+"</a>");
    }
    d.writeln("<ol start="+(start+1)+">");
    for(var i = start; i <= last; i ++) {
        outputOne(d, i);
    }
    d.writeln("</ol>");
    if(last < totalCount - 1) {
        d.writeln("<a href='javascript:opener.showBad"+name+"("+(last + 1)+
                  ");'>Next bad "+name+"</a>");
    }
    codeFrameCode = oldCodeFrameCode;
    d.close();
}

function outputOneBadCast(d, i) {
    d.writeln("<li>" + decodeOneEdge(badCastEdge[i]));
    if(badCastIsSeq[i]) {
        d.writeln("(seq)");
    }
}

function outputOneIncompat(d, i) {
    var theIncompat = incompatClass[i];
    var idx = theIncompat.indexOf(':');
    if(idx < 0 ) {
        alert("The incompatibility data "
              +theIncompat+" does not contain :");
        d.close();
        return;
    }
    var theRepr = theIncompat.substr(0,idx) - 0;
    var extremes = theIncompat.substr(idx+1).split(',');

    d.writeln("<li> incompatible types flow into " + printNode(theRepr));
    d.writeln("<ul>");
    for (var eidx in extremes) {
        // alert("theRepr="+theRepr+" eidx="+extremes[eidx]);
        var nd_edge = extremes[eidx].split('@');
        d.writeln("<li> node "+printNode(nd_edge[0])
                  +" at "+decodeOneEdge(nd_edge[1]));
    }
    d.writeln("</ul>");
}


// Save the current node in a separate window
function saveCurrentNode() {
    if(currentNodeShown == undefined) {
        alert("There is no node shown currently\n"); return;
    }
    // Make a window
    var newWin = window.open("", "saved" + currentNodeShown.nodeNumber,
                             "directories=0,menubar=0,personalbar=0,resizable=1,scrollbars=1,toolbar=0,width=600,height=200");
    var oldCodeFrameCode = codeFrameCode;
    codeFrameCode = "opener";
    outputNodeinfo(newWin.document,currentNodeShown);
    codeFrameCode = oldCodeFrameCode;
}

// Show the cured file
function showCuredFile() {
    log("showing ccured file");
    // Construct the new URL. Drop the .browser/ part
    var newurl = basehref.substr(0, basehref.length - 9) + ".cured.c";
    // Create a new window
    var w = window.open(newurl, "curedfile",
                        "width=800,height=800,resizable=1,scrollbars=1");
}

   

/* Logging support */
function setLogging(isSet) { // Called from the form
    if(isSet) { // Turn logging on
        // Enable logging
        logWindow = window.open("", "log");
        logWindow.document.open();
    } else { // Turn logging off
        // Close the window
        logWindow.close();
        logWindow = undefined;
    }
}

function log() {
    if(logWindow != undefined) {
        logWindow.document.write(log.arguments.join(' '));
    }
}

/**********************************************************
 **********************************************************
 **
 ** ASYNCHRONOUS LOADING OF FILES
 **
 *********************************************************/
// Remember whether we failed because we are waiting for a file to load
var failedBecauseWaitingForFile = false;

// Remember a list of files to be loaded and the frame in which
// they must be loaded 
var nrFilesToLoad = 0;
var filesToLoad = new Array(16);

// Schedule a file for loading
function scheduleFileLoading(fileName, inFrame) {
  // See if it is scheduled already
  if(debugSchedule) {
    alert("Scheduling the loading of "+fileName+" in frame "+inFrame);
  }
  // Maybe we have already scheduled this file for loading
  for(var i=0;i<nrFilesToLoad;i++) {
    if(filesToLoad[i].fileName == fileName) {
      return;
    }
  }
  // Make a new schedule object
  var schedule = new Object;
  schedule.fileName = fileName;
  schedule.inFrame = inFrame;
  filesToLoad[nrFilesToLoad ++] = schedule;
  failedBecauseWaitingForFile = true; // Signal that we need to load files
}

// Remember here a function to retry when we have finished loading all files
var retryThunk = undefined;

/* Declare an entry point (an user-event handler). We try to execute it and 
 * if it fails because it is waiting for a file, we wait and then retry it. */
function entryPoint(thunk) {
  thunk(); // Try it
  // See if we have failed because waiting for data
  if(failedBecauseWaitingForFile) {
    // Schedule this entry point for later
    retryThunk = function ()  { entryPoint(thunk); };
    // And initiate loading the files.
    if(nrFilesToLoad > 0) {
      loadNextFile();
    } else {
        alert("failedBecauseWaitingForFile but no files waiting");
        failedBecauseWaitingForFile = false;
    }
  } else {
    // We have succeeded
      if(frames[dataFrame].document == undefined) {
          alert("Bug: the data document is not present");
      }
      frames[dataFrame].document.writeln("Done\n");
  }
}


// var theTimeoutId;
// Now load one file
function loadNextFile() {
    nrFilesToLoad --;
    // Schedule one file to load
    if(debugSchedule) {
        alert("Loading "+filesToLoad[nrFilesToLoad].fileName
              +" in frame "+filesToLoad[nrFilesToLoad].inFrame);
    }
    // If we are loading in the source frame then we must clear the bullet
    if(filesToLoad[nrFilesToLoad].inFrame == sourceFrame) {
        if (imageMadeBullet != undefined) {
            imageMadeBullet.src = pixel.src;
        }
        imageMadeBullet = undefined;
    }
    frames[filesToLoad[nrFilesToLoad].inFrame].location.href
      = filesToLoad[nrFilesToLoad].fileName;
    // now set a timeout
    //theTimeoutId = top.setTimeout("window.loadTimeOut()", 2000);
}

//// A function that is called
//function loadTimeOut() {
//    // Get the location of the last files loaded. It seems that if
//    // the loading fails then we are going to get a "Permission denied"
//    // error
//    alert("Time is up! status=" + top.status + " location="+theloc);
//}

// An event handler called when a source or data file is loaded
// This function is the onload handler for source and data files
function fileFinishedLoading() {
    // top.clearTimeout(theTimeoutId);
    if(debugSchedule) {
        alert("File finished loading\n");
    }
    // See if there are any more files that must be loaded
    if(nrFilesToLoad > 0) {
        loadNextFile();
        return; // We'll load the rest later
    }
    // No more files to load. Retry the thunk
    failedBecauseWaitingForFile = false;
    if(retryThunk != undefined) {
      if(debugSchedule) {
        alert("Retrying thunk\n");
      }
      var rt = retryThunk;
      retryThunk = undefined;
      rt();
    }
}

/************************************************************/


function loadSourceFileFragment(fidx) {
  // See if it was scheduled or loaded
  if(loadedFragment == fidx) { return; }

  var fileName = basehref + "source__" + fidx + ".html";
  scheduleFileLoading(fileName, sourceFrame);

  // Mark that is has been scheduled or loaded
  loadedFragment = fidx;

  // Go and mark the file name in the 'files' select-box
  var theSelect = frames[formFrame].document.forms.buttons.files;
  theSelect.selectedIndex = fidx;
}

// An event handler for loading a file
function lf(fileIdx) {
  entryPoint(function () { loadSourceFileFragment(fileIdx); });
}


// Load some information about edges or nodes
function loadItemInfo(itemidx, itemlist, itemsPerFile, itemFileLoaded,
                      itemFileBaseName) {
    // Find in which file this lives
    var fileIdx = Math.floor(itemidx / itemsPerFile);
    if(isNaN(fileIdx)) {
        alert("fileIdx = Nan: itemidx="+itemidx+" itemsPerFile="+itemsPerFile);
    }
    // See if this file was already loaded or scheduled for loading
    if(itemFileLoaded[fileIdx]) {
      if(! failedBecauseWaitingForFile) {
        // We have already loaded this file. The item must be undefined
        alert(itemFileBaseName + " " + itemidx + " is not defined!");
      }
     } else {
      // Schedule the file for loading
      var fileName = basehref + itemFileBaseName + "__" + fileIdx + ".html";
      scheduleFileLoading(fileName, dataFrame);
      itemFileLoaded[fileIdx] = true; // Say that we have scheduled it
    }
}

function loadNodeInfo(nodeidx) {
    var node = nodelist[nodeidx];
    if(node != undefined) return node; // Already loaded
    loadItemInfo(nodeidx, nodelist,
                 nodesPerFile, nodeFileLoaded,"node");
    return undefined; // We have failed
}
function loadEdgeInfo(edgeidx) {
    var edge = edgelist[edgeidx];
    if(edge != undefined) return edge;
    loadItemInfo(edgeidx, edgelist,
                 edgesPerFile, edgeFileLoaded,"edge");
    return undefined;
}

function findBasehref(href) {
    // Search backward until you find / or \\
    var last = href.lastIndexOf('/');
    if(last < 0) {
        last = href.lastIndexOf('\\');
    }
    if(last < 0) {
        return "";
    } else {
        return href.substr(0, last + 1); // include the /
    }
}



// Display the globals and types
function showGlobals() {
    var d = window.open("", "globals",
                        "width=400,height=250,resizable=1,scrollbars=1").document;
    entryPoint(function () { displayFeatureArray(d, "globals.html",
                                                 globalslist); });
}
function showTypes() {
    var d = window.open("", "types",
                        "width=400,height=250,resizable=1,scrollbars=1").document;
    entryPoint(function () { displayFeatureArray(d, "types.html",
                                                 typeslist); });
}

function displayFeatureArray(d, fname, data) {
    // See if the array is loaded already
    var len = data.length;
    d.open(); // Clear the document
    if(len > 0 && data[0] == undefined) {
        // We must load the array
        var fileName = basehref + fname;
        scheduleFileLoading(fileName, dataFrame);
        d.write("Loading...");
        return; // Wait until it has loaded
    }
    // The array is loaded. Write out its info
    var i;
    d.write("<ul>\n");
    for(i=0;i<len;i++) {
        var info = data[i];
        var fst = info.lastIndexOf('@');
        var snd = info.lastIndexOf(':');
        if(fst < 0 || snd <= fst) {
            alert("Malformed global/type info "+info);
            d.close();
            return;
        }
        var name = info.substr(0,fst);
        var fileidx = info.substr(fst+1,snd-fst-1);
        var featureidx = info.substr(snd+1);
        d.write("<li><a href='javascript:opener.sf("
                +fileidx+",\"if"+featureidx+"\");'>"
                +name+"</a>\n");
    }
    d.write("</ul>\n");
    d.close();
}


