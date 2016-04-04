importScripts("pipecheck.js")

onmessage = function(e) {
    hello = function(m) {
      console.log(m);
      postMessage({
        "type": "log",
        "message": m});
    }

    var modeldata = e.data.model;
    var testdata = e.data.test;
    try {
      var result = pipecheck.fog(testdata, modeldata);
      postMessage({
        "type": "result",
        "result": result});
    } catch (err) {
      console.log("PipeCheck error");
      console.log(err);
      if (err instanceof Array) {
        if (err[2][1].c == "Litmus Test") {
          postMessage({
            "type": "ltparseerror",
            "row": err[2][2],
            "col": err[2][3]
          });
        } else if (err[2][1].c == "Model") {
          postMessage({
            "type": "modelparseerror",
            "row": err[2][2],
            "col": err[2][3]
          });
        } else {
          postMessage({
            "type": "error",
            "name": "unknown!",
            "message": err
          });
        }
      } else {
        postMessage({
          "type": "error",
          "name": err.name,
          "message": err.message
        });
      }
    }
}
