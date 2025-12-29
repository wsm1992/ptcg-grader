import React, { useState, useRef, useEffect, useCallback, useMemo } from 'react';
import { Upload, Move, RefreshCw, ChevronUp, ChevronDown, ChevronLeft, ChevronRight, Ruler, ArrowLeft, ArrowRight, Loader2, MousePointer2, FileJson, FileImage, Image as ImageIcon } from 'lucide-react';

const MIN_TARGET_WIDTH = 1000, MAX_TARGET_WIDTH = 4096, BASE_TARGET_WIDTH = 1000, MAGNIFIER_SIZE = 225;

const loadImage = src => new Promise((resolve, reject) => {
    const img = new Image();
    img.crossOrigin = "anonymous";
    img.onload = () => resolve(img);
    img.onerror = () => reject(new Error("圖片載入失敗"));
    img.src = src;
});

const Matrix = {
    multiply: (A, B) => {
        const rA = A.length, cA = A[0].length, rB = B.length, cB = B[0].length;
        if (cA !== rB) throw new Error("尺寸不匹配");
        return Array(rA).fill(0).map((_, i) => Array(cB).fill(0).map((_, j) => {
            let sum = 0; for (let k = 0; k < cA; k++) sum += A[i][k] * B[k][j]; return sum;
        }));
    },
    inverse3x3: (M) => {
        const [a,b,c,d,e,f,g,h,i] = M.flat(), det = a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g);
        if (Math.abs(det) < 1e-6) return null;
        const invDet = 1 / det;
        return [
            [(e*i-f*h)*invDet, (c*h-b*i)*invDet, (b*f-c*e)*invDet],
            [(f*g-d*i)*invDet, (a*i-c*g)*invDet, (c*d-a*f)*invDet],
            [(d*h-e*g)*invDet, (b*g-a*h)*invDet, (a*e-b*d)*invDet]
        ];
    },
    solveLinearSystem: (A, B) => {
        const n = A.length, M = A.map((row, i) => [...row, B[i]]);
        for (let k = 0; k < n; k++) {
            let i_max = k, v_max = M[k][k];
            for (let i = k + 1; i < n; i++) if (Math.abs(M[i][k]) > Math.abs(v_max)) { v_max = M[i][k]; i_max = i; }
            if (M[i_max][k] === 0) throw new Error("奇異矩陣");
            [M[k], M[i_max]] = [M[i_max], M[k]];
            for (let i = k + 1; i < n; i++) {
                const f = M[i][k] / M[k][k];
                for (let j = k; j <= n; j++) M[i][j] -= M[k][j] * f;
            }
        }
        const X = Array(n).fill(0);
        for (let i = n - 1; i >= 0; i--) {
            let sum = 0; for (let j = i + 1; j < n; j++) sum += M[i][j] * X[j];
            X[i] = (M[i][n] - sum) / M[i][i];
        }
        return X;
    }
};

const bilinearInterpolation = ({ width, height, data }, x, y) => {
    const x1 = Math.floor(x), y1 = Math.floor(y), x2 = Math.ceil(x), y2 = Math.ceil(y);
    if (x1 < 0 || x2 >= width || y1 < 0 || y2 >= height) return [0, 0, 0, 255];
    const fx = x - x1, fy = y - y1, fx1 = 1 - fx, fy1 = 1 - fy;
    const idx = (px, py) => (py * width + px) * 4;
    let r=0, g=0, b=0, a=0;
    const interp = (i, w) => { r+=data[i]*w; g+=data[i+1]*w; b+=data[i+2]*w; a+=data[i+3]*w; };
    interp(idx(x1, y1), fx1*fy1); interp(idx(x2, y1), fx*fy1);
    interp(idx(x1, y2), fx1*fy); interp(idx(x2, y2), fx*fy);
    return [Math.round(r), Math.round(g), Math.round(b), Math.round(a)];
};

const Magnifier = React.memo(({ magnifierState, zoom, cardImage }) => {
    const { visible, targetX, targetY, imgRect, currentStep, cropPoints, measureLines } = magnifierState;
    const canvasRef = useRef(null);
    const size = useMemo(() => zoom >= 3 ? MAGNIFIER_SIZE * 2 : zoom >= 2 ? MAGNIFIER_SIZE * 1.5 : MAGNIFIER_SIZE, [zoom]);
    const halfSize = size / 2;

    useEffect(() => {
        if (!visible || !canvasRef.current || !cardImage || !imgRect?.width) return;
        const ctx = canvasRef.current.getContext('2d');
        canvasRef.current.width = size; canvasRef.current.height = size;
        ctx.fillStyle = '#000'; ctx.fillRect(0, 0, size, size);

        if (!cardImage.complete) return;
        const imgW = cardImage.naturalWidth, imgH = cardImage.naturalHeight;
        const normX = (targetX - imgRect.left) / imgRect.width, normY = (targetY - imgRect.top) / imgRect.height;
        const srcCX = normX * imgW, srcCY = normY * imgH;
        const srcClipW = size / zoom, srcClipH = size / zoom;
        let srcX = srcCX - srcClipW / 2, srcY = srcCY - srcClipH / 2, dstX = 0, dstY = 0, dstW = size, dstH = size;

        if (srcX < 0) { dstX = -srcX * zoom; dstW -= dstX; srcX = 0; }
        if (srcY < 0) { dstY = -srcY * zoom; dstH -= dstY; srcY = 0; }
        if (srcX + srcClipW > imgW) dstW -= ((srcX + srcClipW) - imgW) * zoom;
        if (srcY + srcClipH > imgH) dstH -= ((srcY + srcClipH) - imgH) * zoom;

        if (dstW > 0 && dstH > 0) ctx.drawImage(cardImage, srcX, srcY, dstW/zoom, dstH/zoom, dstX, dstY, dstW, dstH);

        const transformX = px => (px - srcCX) * zoom + halfSize, transformY = py => (py - srcCY) * zoom + halfSize;
        ctx.lineWidth = 2; ctx.setLineDash([5, 5]);

        if (currentStep === 'crop' && cropPoints?.length === 4) {
            ctx.strokeStyle = '#22c55e'; ctx.beginPath();
            const pts = cropPoints.map(p => ({ x: transformX(p.x * imgW), y: transformY(p.y * imgH) }));
            ctx.moveTo(pts[0].x, pts[0].y);
            pts.slice(1).forEach(p => ctx.lineTo(p.x, p.y));
            ctx.lineTo(pts[0].x, pts[0].y); ctx.stroke();
            ctx.setLineDash([]); ctx.fillStyle = '#22c55e';
            pts.forEach(p => { ctx.beginPath(); ctx.arc(p.x, p.y, 4, 0, Math.PI*2); ctx.fill(); });
        } else if (currentStep === 'measure' && measureLines) {
            const drawLine = (pct, isV, color) => {
                const val = isV ? transformX(pct/100*imgW) : transformY(pct/100*imgH);
                if (val >= 0 && val <= size) {
                    ctx.strokeStyle = color; ctx.beginPath();
                    isV ? ctx.moveTo(val, 0) : ctx.moveTo(0, val);
                    isV ? ctx.lineTo(val, size) : ctx.lineTo(size, val);
                    ctx.stroke();
                }
            };
            const { outerTop, outerBottom, outerLeft, outerRight, innerTop, innerBottom, innerLeft, innerRight } = measureLines;
            [outerTop, outerBottom].forEach(v => drawLine(v, false, '#3b82f6'));
            [outerLeft, outerRight].forEach(v => drawLine(v, true, '#3b82f6'));
            [innerTop, innerBottom].forEach(v => drawLine(v, false, '#ef4444'));
            [innerLeft, innerRight].forEach(v => drawLine(v, true, '#ef4444'));
        }
        ctx.setLineDash([]); ctx.fillStyle = 'rgba(255,0,0,0.8)';
        ctx.beginPath(); ctx.arc(halfSize, halfSize, 3, 0, Math.PI*2); ctx.fill();
    }, [visible, targetX, targetY, imgRect, cardImage, size, zoom, currentStep, cropPoints, measureLines]);

    if (!visible || !imgRect?.width) return null;
    return <div className="fixed rounded-full shadow-2xl z-[100] border-4 border-yellow-400 backdrop-blur-sm overflow-hidden bg-gray-900/50" 
        style={{ left: targetX-halfSize, top: targetY-halfSize, width: size, height: size }}>
        <canvas ref={canvasRef} className="rounded-full w-full h-full"/>
    </div>;
});

function App() {
    const [step, setStep] = useState('upload');
    const [originalImage, setOriginalImage] = useState(null);
    const [originalFileName, setOriginalFileName] = useState("card");
    const [processedImage, setProcessedImage] = useState(null);
    const [isProcessing, setIsProcessing] = useState(false);
    const [zoomLevel, setZoomLevel] = useState(1.0);
    const [loadingText, setLoadingText] = useState("校正中...");
    const [pendingProjectData, setPendingProjectData] = useState(null);
    const [isMagnifierPanelCollapsed, setIsMagnifierPanelCollapsed] = useState(false);
    const [originalCardDims, setOriginalCardDims] = useState({ w: 0, h: 0 });
    const [cropPoints, setCropPoints] = useState([]);
    const [activePointIndex, setActivePointIndex] = useState(null);
    const [lastActivePointIndex, setLastActivePointIndex] = useState(null);
    const [isGeneralDragging, setIsGeneralDragging] = useState(false);
    const [measureLines, setMeasureLines] = useState({ outerTop: 2, innerTop: 12, outerBottom: 98, innerBottom: 88, outerLeft: 3, innerLeft: 13, outerRight: 97, innerRight: 87 });
    
    // 使用 Ref 儲存會變動的座標數據，避免 useEffect 依賴導致監聽器反覆綁定
    const measureLinesRef = useRef(measureLines);
    useEffect(() => { measureLinesRef.current = measureLines; }, [measureLines]);
    
    const cropPointsRef = useRef(cropPoints);
    useEffect(() => { cropPointsRef.current = cropPoints; }, [cropPoints]);

    const [selectedLineId, setSelectedLineId] = useState(null);
    const [draggingLineId, setDraggingLineId] = useState(null);
    const [lastInteractionCoords, setLastInteractionCoords] = useState({});
    const [magnifier, setMagnifier] = useState({ visible: false, targetX: 0, targetY: 0, imgRect: null, currentStep: 'upload', cropPoints: [], measureLines: {}, isTrackingMouse: false });
    const containerRef = useRef(null), imgRef = useRef(null), magnifierTimeoutRef = useRef(null);

    const cardImageForMagnifier = useMemo(() => step === 'crop' ? originalImage : step === 'measure' ? processedImage : null, [step, originalImage, processedImage]);
    const zoomOptions = [0.2, 0.5, 1.0, 1.5, 2, 3, 5];

    const getLiveImageRect = useCallback(() => imgRef.current?.getBoundingClientRect(), []);
    const showFixedMagnifierAt = useCallback((cx, cy) => {
        const imgRect = getLiveImageRect();
        if (!imgRect?.width) return;
        if (magnifierTimeoutRef.current) clearTimeout(magnifierTimeoutRef.current);
        setMagnifier(p => ({ ...p, visible: true, isTrackingMouse: false, targetX: cx, targetY: cy, imgRect, currentStep: step, cropPoints: cropPointsRef.current, measureLines: measureLinesRef.current }));
        magnifierTimeoutRef.current = setTimeout(() => setMagnifier(p => ({ ...p, visible: false })), 2000);
    }, [step, getLiveImageRect]);

    const getLineScreenCenter = useCallback((id) => {
        if (!id || !processedImage) return null;
        const rect = getLiveImageRect();
        if (!rect?.width) return null;
        if (lastInteractionCoords[id]) return lastInteractionCoords[id];
        const val = measureLinesRef.current[id] / 100, isH = id.includes('Top') || id.includes('Bottom');
        return { x: isH ? rect.left + rect.width/2 : rect.left + rect.width*val, y: isH ? rect.top + rect.height*val : rect.top + rect.height/2 };
    }, [processedImage, lastInteractionCoords, getLiveImageRect]);

    const handleZoomChange = useCallback((z) => {
        setZoomLevel(z);
        let tx, ty;
        if (step === 'measure' && selectedLineId) {
            const c = getLineScreenCenter(selectedLineId);
            if (c) { tx = c.x; ty = c.y; }
        } else {
            const r = getLiveImageRect();
            if (r?.width) { tx = r.left + r.width/2; ty = r.top + r.height/2; }
        }
        if (tx !== undefined) showFixedMagnifierAt(tx, ty);
    }, [step, selectedLineId, getLineScreenCenter, getLiveImageRect, showFixedMagnifierAt]);

    const cycleZoom = useCallback(() => {
        const idx = zoomOptions.indexOf(zoomLevel);
        handleZoomChange(zoomOptions[(idx + 1) % zoomOptions.length]);
    }, [zoomLevel, handleZoomChange]);

    const handleReset = () => {
        setStep('upload'); setOriginalImage(null); setProcessedImage(null); setPendingProjectData(null);
        setOriginalFileName("card"); setZoomLevel(1.0); setLastActivePointIndex(null); setSelectedLineId(null);
        setDraggingLineId(null); setIsGeneralDragging(false);
        setMeasureLines({ outerTop: 2, innerTop: 12, outerBottom: 98, innerBottom: 88, outerLeft: 3, innerLeft: 13, outerRight: 97, innerRight: 87 });
    };

    const handleJsonUpload = e => {
        const file = e.target.files[0];
        if (!file) return;
        const reader = new FileReader();
        reader.onload = ev => {
            try {
                const data = JSON.parse(ev.target.result);
                if (data?.cropPoints && data?.measureLines) setPendingProjectData(data);
                else alert("無效的 JSON");
            } catch { alert("讀取失敗"); }
        };
        reader.readAsText(file); e.target.value = '';
    };

    const handleExportJSON = () => {
        if (!originalImage) return;
        const blob = new Blob([JSON.stringify({ version: "1.0", timestamp: Date.now(), imageName: originalFileName, cropPoints, measureLines, results: calculateResults() }, null, 2)], { type: "application/json" });
        const link = document.createElement('a');
        link.download = `${originalFileName.replace(/\.[^/.]+$/, "")}_grading.json`;
        link.href = URL.createObjectURL(blob); link.click();
    };

    const handleImageUpload = async e => {
        const file = e.target.files[0];
        if (!file) return;
        if (file.name.match(/\.(heic|heif)$/i)) {
            setLoadingText("HEIC 轉換中..."); setIsProcessing(true);
            try {
                // 使用 window.heic2any 避免 import 錯誤
                if (!window.heic2any) {
                    await new Promise((resolve, reject) => {
                        const script = document.createElement('script');
                        script.src = "https://cdnjs.cloudflare.com/ajax/libs/heic2any/0.0.4/heic2any.min.js";
                        script.onload = resolve;
                        script.onerror = reject;
                        document.head.appendChild(script);
                    });
                }
                const blob = await window.heic2any({ blob: file, toType: "image/jpeg", quality: 0.8 });
                processImageFile(new File([Array.isArray(blob)?blob[0]:blob], file.name.replace(/\.(heic|heif)$/i, ".jpg"), { type: "image/jpeg" }));
            } catch (err) { 
                console.error(err);
                alert("HEIC 轉換失敗: " + err.message); 
                setIsProcessing(false); 
            }
        } else processImageFile(file);
        e.target.value = '';
    };

    const processImageFile = file => {
        setOriginalFileName(file.name);
        const reader = new FileReader();
        reader.onload = ev => {
            const img = new Image(); img.crossOrigin = "anonymous";
            img.onload = () => {
                setOriginalImage(img); setOriginalCardDims({ w: img.naturalWidth, h: img.naturalHeight });
                if (pendingProjectData) {
                    setCropPoints(pendingProjectData.cropPoints); setMeasureLines(pendingProjectData.measureLines);
                    setPendingProjectData(null);
                } else {
                    setCropPoints([{ x: 0.15, y: 0.15 }, { x: 0.85, y: 0.15 }, { x: 0.85, y: 0.85 }, { x: 0.15, y: 0.85 }]);
                }
                setProcessedImage(null); setStep('crop'); setLastActivePointIndex(null); setIsProcessing(false);
            };
            img.src = ev.target.result;
        };
        reader.readAsDataURL(file);
    };

    const getScreenCoords = useCallback((nx, ny) => {
        const r = getLiveImageRect();
        return r?.width ? { x: nx*r.width+r.left, y: ny*r.height+r.top } : {x:-100,y:-100};
    }, [getLiveImageRect]);

    const handleCropDragStart = (i, e) => {
        e.preventDefault(); e.stopPropagation(); setActivePointIndex(i); setLastActivePointIndex(i); setSelectedLineId(null);
        if (magnifierTimeoutRef.current) clearTimeout(magnifierTimeoutRef.current);
    };

    const handleLineDragStart = (id, e) => {
        e.stopPropagation(); setSelectedLineId(id); setDraggingLineId(id); setActivePointIndex(null);
        const cx = e.touches?e.touches[0].clientX:e.clientX, cy = e.touches?e.touches[0].clientY:e.clientY;
        showFixedMagnifierAt(cx, cy); setLastInteractionCoords(p => ({ ...p, [id]: { x: cx, y: cy } }));
    };

    const handleDragStart = e => {
        setIsGeneralDragging(true);
        const cx = e.touches?e.touches[0].clientX:e.clientX, cy = e.touches?e.touches[0].clientY:e.clientY;
        if(getLiveImageRect()) {
            if(magnifierTimeoutRef.current) clearTimeout(magnifierTimeoutRef.current);
            setMagnifier(p => ({ ...p, visible: true, isTrackingMouse: true, targetX: cx, targetY: cy, imgRect: getLiveImageRect(), measureLines: measureLinesRef.current, currentStep: step }));
        }
    };

    const handleGlobalMove = useCallback(e => {
        if (!containerRef.current) return;
        const cx = e.touches?e.touches[0].clientX:e.clientX, cy = e.touches?e.touches[0].clientY:e.clientY;
        const r = getLiveImageRect();
        if (!r?.width) return;
        const nx = Math.max(0, Math.min(1, (cx - r.left)/r.width)), ny = Math.max(0, Math.min(1, (cy - r.top)/r.height));

        if (step === 'crop' && activePointIndex !== null) {
            if (magnifierTimeoutRef.current) clearTimeout(magnifierTimeoutRef.current);
            // 使用 Ref 獲取最新的 cropPoints，避免依賴 cropPoints 導致 useCallback 改變
            const ncp = [...cropPointsRef.current]; 
            ncp[activePointIndex] = { x: nx, y: ny }; 
            setCropPoints(ncp);
            setMagnifier(p => ({ ...p, visible: true, isTrackingMouse: true, targetX: cx, targetY: cy, imgRect: r, currentStep: step, cropPoints: ncp }));
        } else if (step === 'measure' && draggingLineId) {
            if (magnifierTimeoutRef.current) clearTimeout(magnifierTimeoutRef.current);
            const val = (draggingLineId.includes('Left')||draggingLineId.includes('Right')) ? nx*100 : ny*100;
            setMeasureLines(p => ({ ...p, [draggingLineId]: val }));
            setMagnifier(p => ({ ...p, visible: true, isTrackingMouse: true, targetX: cx, targetY: cy, imgRect: r, measureLines: measureLinesRef.current, currentStep: step }));
            setLastInteractionCoords(p => ({ ...p, [draggingLineId]: { x: cx, y: cy } }));
        } else if (step === 'measure' && isGeneralDragging) {
            if (magnifierTimeoutRef.current) clearTimeout(magnifierTimeoutRef.current);
            setMagnifier(p => ({ ...p, visible: true, isTrackingMouse: true, targetX: cx, targetY: cy, imgRect: r, measureLines: measureLinesRef.current, currentStep: step }));
        }
    }, [step, activePointIndex, draggingLineId, isGeneralDragging, getLiveImageRect]); // 移除 cropPoints 依賴

    const handleGlobalUp = useCallback(() => {
        setActivePointIndex(null); setDraggingLineId(null); setIsGeneralDragging(false);
        setMagnifier(p => ({ ...p, visible: false }));
        if (magnifierTimeoutRef.current) clearTimeout(magnifierTimeoutRef.current);
    }, []);

    useEffect(() => {
        window.addEventListener('mousemove', handleGlobalMove); 
        window.addEventListener('mouseup', handleGlobalUp);
        
        const touchOptions = { passive: false };
        window.addEventListener('touchmove', e => { 
            if(activePointIndex!==null||draggingLineId!==null||isGeneralDragging) e.preventDefault(); 
            handleGlobalMove(e); 
        }, touchOptions);
        
        window.addEventListener('touchend', handleGlobalUp);
        window.addEventListener('touchcancel', handleGlobalUp); // 新增 touchcancel

        return () => { 
            window.removeEventListener('mousemove', handleGlobalMove); 
            window.removeEventListener('mouseup', handleGlobalUp); 
            window.removeEventListener('touchmove', handleGlobalMove); // 這裡 remove 的函數必須是同一個參考
            window.removeEventListener('touchend', handleGlobalUp);
            window.removeEventListener('touchcancel', handleGlobalUp);
        };
    }, [handleGlobalMove, handleGlobalUp, activePointIndex, draggingLineId, isGeneralDragging]);

    const performWarpAndProceed = useCallback(async () => {
        if (!originalImage?.src) return;
        setLoadingText("校正中..."); setIsProcessing(true);
        try {
            const sw = originalCardDims.w, sh = originalCardDims.h;
            const dist = (a, b) => Math.sqrt(Math.pow((a.x-b.x)*sw,2) + Math.pow((a.y-b.y)*sh,2));
            const aw = (dist(cropPoints[0],cropPoints[1]) + dist(cropPoints[3],cropPoints[2]))/2;
            const ah = (dist(cropPoints[0],cropPoints[3]) + dist(cropPoints[1],cropPoints[2]))/2;
            const tw = Math.max(MIN_TARGET_WIDTH, Math.min(MAX_TARGET_WIDTH, Math.round(aw))), th = Math.round(tw / (aw/ah));
            const src = cropPoints.map(p=>[p.x*sw, p.y*sh]), dst = [[0,0],[tw,0],[tw,th],[0,th]];
            const A=[], B=[];
            for(let i=0;i<4;i++){ const [x,y]=src[i],[u,v]=dst[i]; A.push([x,y,1,0,0,0,-u*x,-u*y],[0,0,0,x,y,1,-v*x,-v*y]); B.push(u,v); }
            const sol = Matrix.solveLinearSystem(A,B);
            const H_inv = Matrix.inverse3x3([sol.slice(0,3), sol.slice(3,6), [...sol.slice(6,8),1]]);
            if(!H_inv) throw new Error("奇異");

            const cvs = document.createElement('canvas'); cvs.width=tw; cvs.height=th;
            const ctx = cvs.getContext('2d'), tmpCvs = document.createElement('canvas'), tmpCtx = tmpCvs.getContext('2d');
            tmpCvs.width=sw; tmpCvs.height=sh;
            tmpCtx.drawImage(await loadImage(originalImage.src),0,0,sw,sh);
            const sDat = tmpCtx.getImageData(0,0,sw,sh), dDat = ctx.createImageData(tw,th), dd = dDat.data;

            for(let y=0;y<th;y++) for(let x=0;x<tw;x++) {
                const vec = Matrix.multiply(H_inv, [[x],[y],[1]]), w=vec[2][0], sx=vec[0][0]/w, sy=vec[1][0]/w, di=(y*tw+x)*4;
                if(sx>=0 && sx<sw-1 && sy>=0 && sy<sh-1) {
                    const [r,g,b,a] = bilinearInterpolation(sDat, sx, sy);
                    dd[di]=r; dd[di+1]=g; dd[di+2]=b; dd[di+3]=a;
                } else { dd[di]=dd[di+1]=dd[di+2]=0; dd[di+3]=255; }
            }
            ctx.putImageData(dDat,0,0);
            const ni = new Image(); ni.onload = () => { setProcessedImage(ni); setIsProcessing(false); setStep('measure'); setSelectedLineId(null); if(containerRef.current) containerRef.current.scrollTop=0; };
            ni.src = cvs.toDataURL();
        } catch (e) { console.error(e); setIsProcessing(false); }
    }, [originalImage, originalCardDims, cropPoints]);

    const calculateResults = () => {
        const { innerTop, outerTop, outerBottom, innerBottom, innerLeft, outerLeft, outerRight, innerRight } = measureLines;
        const tv = Math.abs(innerTop-outerTop) + Math.abs(outerBottom-innerBottom) || 1, th = Math.abs(innerLeft-outerLeft) + Math.abs(outerRight-innerRight) || 1;
        return { v: { top: Math.abs(innerTop-outerTop)/tv*100, bottom: Math.abs(outerBottom-innerBottom)/tv*100 }, h: { left: Math.abs(innerLeft-outerLeft)/th*100, right: Math.abs(outerRight-innerRight)/th*100 } };
    };
    const results = calculateResults();

    const nudgeLine = (dir) => {
        if (!selectedLineId || !processedImage || !getLiveImageRect()) return;
        const isH = selectedLineId.includes('Top') || selectedLineId.includes('Bottom');
        const px = (zoomLevel>=5?0.2:zoomLevel>=3?0.5:zoomLevel>=2?1:5) * (1/(isH?processedImage.naturalHeight:processedImage.naturalWidth)*100);
        const nv = Math.max(0, Math.min(100, measureLines[selectedLineId] + dir*px));
        setMeasureLines(p => ({ ...p, [selectedLineId]: nv }));
        const r = getLiveImageRect(), lc = lastInteractionCoords[selectedLineId];
        const tx = isH ? Math.max(r.left, Math.min(r.right, lc?.x||(r.left+r.width/2))) : r.left+r.width*(nv/100);
        const ty = isH ? r.top+r.height*(nv/100) : Math.max(r.top, Math.min(r.bottom, lc?.y||(r.top+r.height/2)));
        setLastInteractionCoords(p => ({ ...p, [selectedLineId]: { x: tx, y: ty } })); showFixedMagnifierAt(tx, ty);
    };

    const nudgeCropPoint = (dx, dy) => {
        if (lastActivePointIndex === null || !originalCardDims.w) return;
        const px = zoomLevel>=5?0.2:zoomLevel>=3?0.5:zoomLevel>=2?1:5;
        const nx = (dx*px)/originalCardDims.w, ny = (dy*px)/originalCardDims.h;
        setCropPoints(p => { const np=[...p], pt=np[lastActivePointIndex]; np[lastActivePointIndex]={x:Math.max(0,Math.min(1,pt.x+nx)),y:Math.max(0,Math.min(1,pt.y+ny))}; return np; });
        const r = imgRef.current?.getBoundingClientRect();
        if(r) { const pt=cropPoints[lastActivePointIndex]; showFixedMagnifierAt(r.left+(pt.x+nx)*r.width, r.top+(pt.y+ny)*r.height); }
    };

    const downloadResultImage = () => {
        if (!processedImage) return;
        const cvs = document.createElement('canvas'), ctx = cvs.getContext('2d'), w = processedImage.naturalWidth, h = processedImage.naturalHeight;
        cvs.width = w; cvs.height = h + 120; ctx.fillStyle = '#111827'; ctx.fillRect(0,0,w,cvs.height); ctx.drawImage(processedImage,0,0);
        const dl = (v, isH, c) => { ctx.strokeStyle=c; ctx.lineWidth=3; ctx.setLineDash([10,10]); ctx.beginPath(); isH?ctx.moveTo(0,v/100*h):ctx.moveTo(v/100*w,0); isH?ctx.lineTo(w,v/100*h):ctx.lineTo(v/100*w,h); ctx.stroke(); };
        const {outerTop,outerBottom,outerLeft,outerRight,innerTop,innerBottom,innerLeft,innerRight}=measureLines;
        [outerTop,outerBottom].forEach(v=>dl(v,true,'#3b82f6')); [outerLeft,outerRight].forEach(v=>dl(v,false,'#3b82f6'));
        [innerTop,innerBottom].forEach(v=>dl(v,true,'#ef4444')); [innerLeft,innerRight].forEach(v=>dl(v,false,'#ef4444'));
        ctx.setLineDash([]); ctx.fillStyle='#fff'; ctx.font='bold 32px sans-serif'; ctx.textAlign='center';
        ctx.fillText(`左右 (H): ${results.h.left.toFixed(1)} : ${results.h.right.toFixed(1)}`, w*0.25, h+70);
        ctx.fillText(`上下 (V): ${results.v.top.toFixed(1)} : ${results.v.bottom.toFixed(1)}`, w*0.75, h+70);
        ctx.strokeStyle='#374151'; ctx.beginPath(); ctx.moveTo(w/2,h+20); ctx.lineTo(w/2,h+100); ctx.stroke();
        const a = document.createElement('a'); a.download = `${originalFileName.replace(/\.[^/.]+$/, "")}_grading.png`; a.href = cvs.toDataURL(); a.click();
    };

    const renderLine = (id, ori, cls, inn) => {
        const val = measureLines[id], act = selectedLineId===id, isH = ori==='horizontal';
        return <div key={id} className={`absolute z-20 group ${isH?'cursor-row-resize':'cursor-col-resize'}`} style={{ [isH?'top':'left']:`${val}%`, [isH?'left':'top']:0, [isH?'right':'bottom']:0, [isH?'height':'width']:0 }}
            onMouseDown={e=>handleLineDragStart(id,e)} onTouchStart={e=>handleLineDragStart(id,e)}>
            <div className={`absolute w-full h-full border border-dashed transition-colors ${isH?'border-t':'border-l'} ${act?'border-yellow-400 z-50 shadow-[0_0_5px_rgba(255,255,0,0.8)]':cls}`}/>
            <div className="absolute bg-transparent" style={isH?{top:-10,bottom:-10,left:0,right:0}:{left:-10,right:-10,top:0,bottom:0}}/>
            {act && <div className={`absolute ${isH?'left-1/2 -top-6 -translate-x-1/2':'top-1/2 -left-6 -translate-y-1/2'} bg-gray-900 text-[10px] text-white px-1 rounded pointer-events-none whitespace-nowrap`}>{inn?'紅線':'藍線'}</div>}
        </div>;
    };
    const [coordsKey, setCoordsKey] = useState(0); 
    
    // Fixed: Added block body and cleanup function for useEffect
    useEffect(() => {
        const timer = setTimeout(() => setCoordsKey(k => k + 1), 50);
        return () => clearTimeout(timer);
    }, [step]);

    return (
        <div className="h-screen bg-gray-950 text-white font-sans flex flex-col overflow-hidden">
            <header className="bg-gray-900 border-b border-gray-800 h-12 flex items-center justify-between px-4 shrink-0 z-50">
                <div className="flex items-center gap-2"><Ruler className="text-blue-400" size={18}/><span className="font-bold text-sm bg-gradient-to-r from-blue-400 to-purple-400 bg-clip-text text-transparent">PTCG Grade</span></div>
                <div className="flex items-center gap-2 text-xs">{step!=='upload' && <button onClick={handleReset} className="hover:text-white text-gray-400 flex items-center gap-1"><RefreshCw size={12}/>重置</button>}</div>
            </header>
            <main className="flex-1 relative w-full overflow-auto select-none p-2 md:p-6 flex justify-center items-start">
                {step === 'upload' ? (
                    <div className="flex-1 flex flex-col items-center justify-start pt-12 md:justify-center md:pt-0 w-full max-w-4xl gap-6 p-6">
                        {pendingProjectData && <div className="bg-green-900/20 border border-green-500/30 p-3 rounded-lg text-center w-full max-w-sm"><div className="flex justify-center gap-2 text-green-400 font-bold text-sm"><FileJson size={16}/><span>設定就緒</span></div><div className="text-gray-400 text-xs">{pendingProjectData.imageName}</div></div>}
                        <div className={`w-full max-w-md aspect-[3/4] border-2 border-dashed rounded-2xl relative flex flex-col items-center justify-center group cursor-pointer shadow-2xl p-6 ${pendingProjectData?'border-green-500/50 bg-green-900/10':'border-gray-700 bg-gray-900 hover:border-blue-500'}`}>
                            {pendingProjectData ? <FileImage size={64} className="text-green-500/80 mb-6 animate-pulse"/> : <Upload size={64} className="text-gray-600 group-hover:text-blue-400 mb-6"/>}
                            <input type="file" accept="image/*,.heic,.heif" onChange={handleImageUpload} className="absolute inset-0 opacity-0 cursor-pointer z-10"/>
                            <p className={`font-bold text-xl mb-2 ${pendingProjectData?'text-green-400':'text-gray-300'}`}>{pendingProjectData?'上傳對應圖片':'上傳卡牌照片'}</p>
                        </div>
                        {!pendingProjectData ? <div className="relative group"><button className="flex items-center gap-2 text-gray-400 px-5 py-2 rounded-full border border-gray-700 bg-gray-800/50 text-sm"><FileJson size={16}/>載入專案</button><input type="file" accept=".json" onChange={handleJsonUpload} className="absolute inset-0 opacity-0 cursor-pointer"/></div> : <button onClick={()=>setPendingProjectData(null)} className="text-gray-600 text-xs">取消</button>}
                    </div>
                ) : (
                    <div className={`flex-shrink-0 select-none ${step==='measure'?'max-h-[85vh] overflow-y-auto bg-gray-800 rounded-xl p-2 w-fit max-w-full':'relative w-fit h-fit'}`} ref={containerRef}>
                        <div className="relative w-fit h-fit">
                            <img ref={imgRef} src={step==='crop'?originalImage?.src:processedImage?.src} className="object-contain pointer-events-none shadow-2xl" style={step==='crop'?{maxWidth:BASE_TARGET_WIDTH,maxHeight:'80vh'}:{width:processedImage?.naturalWidth,height:'auto'}}/>
                            <div className={`fixed right-2 top-1/2 -translate-y-1/2 bg-gray-800/90 backdrop-blur rounded-lg shadow-xl z-[110] flex flex-col gap-2 border border-gray-700 transition-all ${isMagnifierPanelCollapsed?'p-2 w-10':'p-3'}`}>
                                <button onClick={()=>setIsMagnifierPanelCollapsed(!isMagnifierPanelCollapsed)} className="self-end text-gray-400 mb-1">{isMagnifierPanelCollapsed?<ChevronLeft size={16}/>:<ChevronRight size={16}/>}</button>
                                {!isMagnifierPanelCollapsed ? <>{zoomOptions.map(z=><button key={z} onClick={()=>handleZoomChange(z)} className={`w-10 h-10 text-xs font-bold rounded border ${zoomLevel===z?'bg-blue-600 text-white border-blue-400':'bg-gray-700 text-gray-300 border-gray-600'}`}>{z}X</button>)}</> : <button onClick={cycleZoom} className="text-[10px] text-blue-400 font-bold">{zoomLevel}X</button>}
                            </div>
                            {step==='crop' && originalImage && <CropOverlay cropPoints={cropPoints} getImageContainerRect={getLiveImageRect} getScreenCoords={getScreenCoords} activePointIndex={activePointIndex} lastActivePointIndex={lastActivePointIndex} handleCropDragStart={handleCropDragStart} imgRef={imgRef} key={coordsKey}/>}
                            {step==='measure' && processedImage && <div className="absolute inset-0 w-full h-full cursor-crosshair" onMouseDown={handleDragStart} onTouchStart={handleDragStart}>
                                {renderLine('outerTop','horizontal','border-blue-500',0)}{renderLine('outerBottom','horizontal','border-blue-500',0)}
                                {renderLine('outerLeft','vertical','border-blue-500',0)}{renderLine('outerRight','vertical','border-blue-500',0)}
                                {renderLine('innerTop','horizontal','border-red-500',1)}{renderLine('innerBottom','horizontal','border-red-500',1)}
                                {renderLine('innerLeft','vertical','border-red-500',1)}{renderLine('innerRight','vertical','border-red-500',1)}
                            </div>}
                        </div>
                        {isProcessing && <div className="fixed inset-0 bg-black/80 z-50 flex flex-col items-center justify-center text-white"><Loader2 className="animate-spin mb-4"/><p>{loadingText}</p></div>}
                    </div>
                )}
            </main>
            <Magnifier magnifierState={{...magnifier, cropPoints, measureLines, currentStep: step}} zoom={zoomLevel} cardImage={cardImageForMagnifier}/>
            <footer className="bg-gray-900 border-t border-gray-800 p-3 shrink-0 relative">
                <div className="max-w-4xl mx-auto w-full relative z-[120]">
                    {step === 'crop' ? (
                        <div className="flex flex-col md:flex-row items-center justify-between gap-3">
                            <div className="text-gray-400 text-xs"><span className="text-green-400 font-bold">Step 1:</span> 拖曳綠點至四角</div>
                            <div className="flex items-center gap-2 bg-gray-800/50 p-1.5 rounded-lg border border-gray-700">
                                <div className="flex flex-col items-center gap-1">
                                    <button onClick={()=>nudgeCropPoint(0,-1)} disabled={lastActivePointIndex===null} className="w-8 h-8 bg-gray-700 rounded flex items-center justify-center disabled:opacity-30"><ChevronUp size={16}/></button>
                                    <div className="flex gap-1"><button onClick={()=>nudgeCropPoint(-1,0)} disabled={lastActivePointIndex===null} className="w-8 h-8 bg-gray-700 rounded flex items-center justify-center disabled:opacity-30"><ChevronLeft size={16}/></button><div className="w-8 h-8 flex items-center justify-center text-blue-400">{lastActivePointIndex!==null?<Move size={16}/>:<MousePointer2 size={16}/>}</div><button onClick={()=>nudgeCropPoint(1,0)} disabled={lastActivePointIndex===null} className="w-8 h-8 bg-gray-700 rounded flex items-center justify-center disabled:opacity-30"><ChevronRight size={16}/></button></div>
                                    <button onClick={()=>nudgeCropPoint(0,1)} disabled={lastActivePointIndex===null} className="w-8 h-8 bg-gray-700 rounded flex items-center justify-center disabled:opacity-30"><ChevronDown size={16}/></button>
                                </div>
                            </div>
                            <button onClick={performWarpAndProceed} className="bg-green-600 text-white px-6 py-2 rounded-full font-bold shadow flex items-center gap-2">校正並繼續 <ArrowRight size={18}/></button>
                        </div>
                    ) : step === 'measure' && (
                        <div className="flex flex-col gap-3">
                            <div className="flex justify-between items-center"><button onClick={()=>setStep('crop')} className="text-gray-500 hover:text-white text-xs flex gap-1"><ArrowLeft size={14}/>重調</button>
                            <div className="flex gap-2 items-center"><button onClick={()=>nudgeLine(-1)} disabled={!selectedLineId} className="w-10 h-10 rounded-full border border-gray-700 flex justify-center items-center disabled:opacity-30">
                            {/* Logic to change chevron type based on selected line */}
                            {selectedLineId && (selectedLineId.includes('Top') || selectedLineId.includes('Bottom')) ? <ChevronUp size={20}/> : <ChevronLeft size={20}/>}
                            </button><span className="text-xs font-bold text-blue-300 w-24 text-center">{selectedLineId?`${measureLines[selectedLineId].toFixed(2)}%`:'微調'}</span><button onClick={()=>nudgeLine(1)} disabled={!selectedLineId} className="w-10 h-10 rounded-full border border-gray-700 flex justify-center items-center disabled:opacity-30">
                            {selectedLineId && (selectedLineId.includes('Top') || selectedLineId.includes('Bottom')) ? <ChevronDown size={20}/> : <ChevronRight size={20}/>}
                            </button></div>
                            <div className="flex gap-2"><button onClick={handleExportJSON} className="bg-blue-600 p-2 rounded text-white"><FileJson size={20}/></button><button onClick={downloadResultImage} className="bg-emerald-600 p-2 rounded text-white"><ImageIcon size={20}/></button></div></div>
                            <div className="bg-black/40 rounded p-2 flex justify-around border border-gray-700 text-sm font-bold"><span className={Math.abs(results.h.left-results.h.right)<=10?'text-green-400':'text-yellow-400'}>H: {results.h.left.toFixed(1)}:{results.h.right.toFixed(1)}</span><span className={Math.abs(results.v.top-results.v.bottom)<=10?'text-green-400':'text-yellow-400'}>V: {results.v.top.toFixed(1)}:{results.v.bottom.toFixed(1)}</span></div>
                        </div>
                    )}
                </div>
            </footer>
        </div>
    );
}

const CropOverlay = ({ cropPoints, getImageContainerRect, getScreenCoords, activePointIndex, lastActivePointIndex, handleCropDragStart, imgRef }) => {
    const rect = getImageContainerRect() || imgRef.current?.getBoundingClientRect();
    if (!rect?.width) return null;
    const pts = cropPoints.map((p, i) => ({ c: getScreenCoords(p.x, p.y), p, i }));
    return <>
        <svg className="absolute inset-0 w-full h-full pointer-events-none"><polygon points={pts.map(k => `${k.c.x-rect.left},${k.c.y-rect.top}`).join(' ')} fill="rgba(34,197,94,0.1)" stroke="rgba(34,197,94,0.8)" strokeWidth="2" strokeDasharray="5"/></svg>
        {pts.map(({ p, i }) => <div key={i} className={`absolute w-8 h-8 -ml-4 -mt-4 rounded-full border-2 cursor-move flex items-center justify-center shadow pointer-events-auto ${activePointIndex===i?'bg-green-400 scale-125 z-30':lastActivePointIndex===i?'bg-green-500 border-yellow-400 scale-110 z-25':'bg-green-500/80 border-green-200 z-20'}`} style={{ left: `${p.x*100}%`, top: `${p.y*100}%`, touchAction:'none' }} onMouseDown={e=>handleCropDragStart(i,e)} onTouchStart={e=>handleCropDragStart(i,e)}><Move size={14} className={lastActivePointIndex===i?"text-yellow-100":"text-black"}/></div>)}
    </>;
};

export default App;