importScripts("viz.js")

onmessage = function(e) {
  try {
    var graph = Viz(e.data);
    postMessage({
      "result": "success",
      "graph": graph
    });
  } catch (err) {
    postMessage({
      "result": "error",
      "msg": err
    });
  }
}
