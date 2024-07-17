function graphT(T, F, xmin,xmax  ){
    graphID++;
    //document.getElementsByClassName("content")[0].innerHTML +=`<canvas id='canvas${graphID}' width=400 height=400 style='border:1px black solid'></canvas>`
    
    var div = document.createElement('canvas');
    div.id = `canvas${graphID}`;
    div.width=400
    div.height=400
    div.style="border:1px black solid"

    //document.getElementsByClassName("content")[0].appendChild(div);
    insertAfter(output,div)
    
    canvas=document.getElementById(`canvas${graphID}`)
    dc=canvas.getContext("2d")
    W=400
    imageData = dc.getImageData(0,0,W,W)
    data = imageData.data
    for(var x=0;x<W;x++){
        for(var y=0;y<W;y++){
            data[4*(y*W+x)] = 255
            data[4*(y*W+x)+1] = 255
            data[4*(y*W+x)+2] = 128
            data[4*(y*W+x)+3] = 255
        }
    }
    var s = (xmax-xmin)/W
    var n = new C("X",T);
    n.fastValue = ()=>window.xVal;
    n.liveVal=true;
    var Fn =  F(n);
    console.log(fill(Fn.toString()))
    var line=true;
    if(line){
        for(var x=0;x<W;x++){
            window.xVal = xmin + x * s;
            //n.fastValue = window.xVal;
            //console.log(Fn.kind)
            var yVal = Fn.float();
            //console.log(yVal)
            var y = W-1-Math.floor(yVal/s+W/2);
            data[4*(y*W+x)] = 0
            data[4*(y*W+x)+1] = 0
            data[4*(y*W+x)+2] = 0
            data[4*(y*W+x)+3] = 255
        }
    }else{
        for(var y=0;y<W;y++){
            for(var x=0;x<W;x++){
                var yVal0 = (y-(W/2))*s
                window.xVal = xmin + x * s;
                //n.fastValue = window.xVal;
                //console.log(Fn.kind)
                var yVal = Fn.float();
                //console.log(yVal)
                //var y = Math.floor(yVal/s+W/2);
                var R = yVal < yVal0 ? 255:0
                data[4*(y*W+x)] = R
                data[4*(y*W+x)+1] = R
                data[4*(y*W+x)+2] = 255-R
                data[4*(y*W+x)+3] = 255
            }
        }
    }

    dc.putImageData(imageData,0,0)
    return 0;
}
//graph(Sin,-3,3)

//toCauchy(deriv(Real.Exp)(Real.fromRat.def(3)))(100)
//sum(Rat, FUN(Nat, n=> Rat.mk(Int.one, Int.mk( factorial(n) ,0) ) ) ,10)  